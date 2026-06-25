#!/bin/bash

# Script to run cvc5 and z3 in parallel on all SMT2 files with timeout and portfolio settings
# Usage: ./prove.sh <smt2_directory> [timeout_seconds] [portfolio_jobs]

set -e
set +m  # Disable job control messages to suppress termination notices

# Check if directory argument is provided
if [ $# -eq 0 ]; then
    echo "Error: Directory argument required"
    echo "Usage: $0 <smt2_directory> [timeout_seconds] [portfolio_jobs]"
    exit 1
fi

# Configuration
SMT2_DIR="$1"
TIMEOUT_SECONDS="${2:-60}"  # Use second argument if provided, otherwise default to 60
PORTFOLIO_JOBS="${3:-8}"    # Use third argument if provided, otherwise default to 8

# Validate timeout is a positive number
if ! [[ "$TIMEOUT_SECONDS" =~ ^[0-9]+$ ]] || [ "$TIMEOUT_SECONDS" -le 0 ]; then
    echo "Error: Timeout must be a positive integer"
    echo "Usage: $0 <smt2_directory> [timeout_seconds] [portfolio_jobs]"
    exit 1
fi

# Validate portfolio-jobs is a positive number
if ! [[ "$PORTFOLIO_JOBS" =~ ^[0-9]+$ ]] || [ "$PORTFOLIO_JOBS" -le 0 ]; then
    echo "Error: Portfolio jobs must be a positive integer"
    echo "Usage: $0 <smt2_directory> [timeout_seconds] [portfolio_jobs]"
    exit 1
fi

CVC5_CMD="cvc5 --use-portfolio --portfolio-jobs $PORTFOLIO_JOBS"
Z3_CMD="z3"

# Ensure directory ends with / for consistency
if [ "${SMT2_DIR: -1}" != "/" ]; then
    SMT2_DIR="${SMT2_DIR}/"
fi

# Validate that directory exists
if [ ! -d "$SMT2_DIR" ]; then
    echo "Error: Directory '$SMT2_DIR' does not exist"
    exit 1
fi

# Sanitize directory name for use in cache file names
# Replace / with _ and remove trailing _
safe_dir_name=$(echo "$SMT2_DIR" | tr '/' '_' | sed 's/_$//' | sed 's/^_//')

# Create output directory for all files (cache, results, summary)
OUTPUT_DIR="output_${safe_dir_name}/"
mkdir -p "$OUTPUT_DIR"

# Create directory-specific cache and result files
RESULTS_FILE="${OUTPUT_DIR}results_${safe_dir_name}.txt"
SUMMARY_FILE="${OUTPUT_DIR}summary_${safe_dir_name}.txt"
CACHE_FILE="${OUTPUT_DIR}unsat_cache_${safe_dir_name}.txt"
SAT_CACHE_FILE="${OUTPUT_DIR}sat_cache_${safe_dir_name}.txt"
TIMESTAMP_CACHE_FILE="${OUTPUT_DIR}timestamp_cache_${safe_dir_name}.txt"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Initialize counters
total_files=0
sat_count=0
unsat_count=0
timeout_count=0
error_count=0
unknown_count=0
cached_sat_count=0
cached_unsat_count=0

# Arrays to store results
sat_files=()
unsat_files=()
timeout_files=()
error_files=()
unknown_files=()
cached_sat_files=()
cached_unsat_files=()

# Cleanup function to kill all cvc5 and z3 processes
cleanup_processes() {
    # Kill all cvc5 processes (suppress errors)
    pkill -9 cvc5 2>/dev/null || true
    
    # Kill all z3 processes (suppress errors)
    pkill -9 z3 2>/dev/null || true
    
    # Wait briefly for processes to terminate
    sleep 0.5 2>/dev/null || sleep 0.5
    
    # Double-check and force kill any remaining processes
    pgrep -f "cvc5" >/dev/null 2>&1 && pkill -9 -f "cvc5" 2>/dev/null || true
    pgrep -f "^z3 " >/dev/null 2>&1 && pkill -9 -f "^z3 " 2>/dev/null || true
}

# Set up trap to cleanup on exit (normal, error, interrupt, or termination)
trap cleanup_processes EXIT INT TERM

echo -e "${BLUE}Starting parallel cvc5/z3 benchmark on SMT2 files...${NC}"
echo "Directory: $SMT2_DIR"
echo "Timeout: ${TIMEOUT_SECONDS}s per file"
echo "cvc5 Command: $CVC5_CMD"
echo "z3 Command: $Z3_CMD"
echo "Running both solvers in parallel"
echo "=========================================="

# Create results file
echo "Parallel cvc5/z3 Benchmark Results - $(date)" > "$RESULTS_FILE"
echo "==========================================" >> "$RESULTS_FILE"
echo "" >> "$RESULTS_FILE"

# Ensure cache files exist
touch "$CACHE_FILE"
touch "$SAT_CACHE_FILE"
touch "$TIMESTAMP_CACHE_FILE"

# Function to check if a file has changed since last proof
# Returns 0 if file has changed or was never proven, 1 if unchanged
check_file_changed() {
    local file_path="$1"
    local filename="$2"
    
    # Get current file modification time
    if [ ! -f "$file_path" ]; then
        return 0  # File doesn't exist, treat as changed
    fi
    
    # Try GNU stat first: Linux stat -f prints to stdout then fails, corrupting $(...) if listed first.
    local current_mtime=$(stat -c %Y "$file_path" 2>/dev/null || stat -f %m "$file_path" 2>/dev/null || echo "0")
    
    # Get cached timestamp (escape filename for safe regex matching)
    local escaped_filename=$(printf '%s\n' "$filename" | sed 's/[[\.*^$()+?{|]/\\&/g')
    local cached_timestamp=$(grep "^${escaped_filename}:" "$TIMESTAMP_CACHE_FILE" 2>/dev/null | cut -d: -f2- | tr -d '[:space:]' || echo "")
    
    # If no cached timestamp, file has changed (never proven)
    if [ -z "$cached_timestamp" ]; then
        return 0
    fi
    
    # Compare timestamps (using string comparison since they're integers)
    if [ "$current_mtime" != "$cached_timestamp" ]; then
        return 0  # File has changed
    else
        return 1  # File unchanged
    fi
}

# Function to update timestamp cache
update_timestamp_cache() {
    local filename="$1"
    local file_path="$2"
    
    # Get current file modification time
    # Try GNU stat first: Linux stat -f prints to stdout then fails, corrupting $(...) if listed first.
    local current_mtime=$(stat -c %Y "$file_path" 2>/dev/null || stat -f %m "$file_path" 2>/dev/null || echo "0")
    
    # Remove old entry if it exists (escape filename for safe regex matching)
    local escaped_filename=$(printf '%s\n' "$filename" | sed 's/[[\.*^$()+?{|]/\\&/g')
    grep -v "^${escaped_filename}:" "$TIMESTAMP_CACHE_FILE" > "${TIMESTAMP_CACHE_FILE}.tmp" 2>/dev/null || true
    mv "${TIMESTAMP_CACHE_FILE}.tmp" "$TIMESTAMP_CACHE_FILE" 2>/dev/null || true
    
    # Add new entry
    echo "${filename}:${current_mtime}" >> "$TIMESTAMP_CACHE_FILE"
}

# Process each SMT2 file
# Save stderr and redirect to suppress job control termination messages
exec 3>&2  # Save stderr to fd 3
exec 2>/dev/null  # Redirect stderr to suppress job control messages
for smt2_file in "$SMT2_DIR"/*.smt2; do
    if [ ! -f "$smt2_file" ]; then
        continue
    fi
    
    filename=$(basename "$smt2_file")
    exec 2>&3  # Restore stderr for echo commands
    
    # Check if file has changed since last proof
    file_changed=false
    if check_file_changed "$smt2_file" "$filename"; then
        file_changed=true
        # Remove from cache files if it exists (file has changed)
        if grep -Fxq "$filename" "$CACHE_FILE"; then
            grep -vFx "$filename" "$CACHE_FILE" > "${CACHE_FILE}.tmp" 2>/dev/null || true
            mv "${CACHE_FILE}.tmp" "$CACHE_FILE" 2>/dev/null || true
        fi
        if grep -Fxq "$filename" "$SAT_CACHE_FILE"; then
            grep -vFx "$filename" "$SAT_CACHE_FILE" > "${SAT_CACHE_FILE}.tmp" 2>/dev/null || true
            mv "${SAT_CACHE_FILE}.tmp" "$SAT_CACHE_FILE" 2>/dev/null || true
        fi
    fi
    
    # Skip if cached as UNSAT and file hasn't changed
    if [ "$file_changed" = false ] && grep -Fxq "$filename" "$CACHE_FILE"; then
        echo -e "${BLUE}Skipping $filename (cached UNSAT)${NC}"
        cached_unsat_count=$((cached_unsat_count + 1))
        cached_unsat_files+=("$filename")
        exec 2>/dev/null  # Redirect stderr again
        continue
    fi
    
    # Skip if cached as SAT and file hasn't changed
    if [ "$file_changed" = false ] && grep -Fxq "$filename" "$SAT_CACHE_FILE"; then
        echo -e "${BLUE}Skipping $filename (cached SAT)${NC}"
        cached_sat_count=$((cached_sat_count + 1))
        cached_sat_files+=("$filename")
        exec 2>/dev/null  # Redirect stderr again
        continue
    fi
    
    total_files=$((total_files + 1))
    echo -n "Proving $filename... "
    exec 2>/dev/null  # Redirect stderr to suppress job control messages
    
    # Create temporary files for output and status (sanitize filename for use in paths)
    safe_filename=$(echo "$filename" | tr '/' '_' | tr ' ' '_')
    cvc5_output="/tmp/cvc5_output_$$_$safe_filename"
    z3_output="/tmp/z3_output_$$_$safe_filename"
    cvc5_status="/tmp/cvc5_status_$$_$safe_filename"
    z3_status="/tmp/z3_status_$$_$safe_filename"
    
    # Start both commands in parallel
    (timeout $TIMEOUT_SECONDS $CVC5_CMD < "$smt2_file" > "$cvc5_output" 2>&1; echo $? > "$cvc5_status") &
    cvc5_pid=$!
    (timeout $TIMEOUT_SECONDS $Z3_CMD "$smt2_file" > "$z3_output" 2>&1; echo $? > "$z3_status") &
    z3_pid=$!
    
    # Monitor both processes with a maximum wait time
    final_result=""
    cvc5_done=false
    z3_done=false
    cvc5_result=""
    z3_result=""
    cvc5_exit_code=""
    z3_exit_code=""
    cvc5_killed=false
    z3_killed=false
    start_time=$(date +%s)
    max_wait_time=$((TIMEOUT_SECONDS + 2))  # Add 2 seconds buffer for process cleanup
    
    while true; do
        current_time=$(date +%s)
        elapsed=$((current_time - start_time))
        
        # Timeout the monitoring loop if it's been too long
        if [ $elapsed -gt $max_wait_time ]; then
            # Force kill any remaining processes
            if kill -0 $cvc5_pid 2>/dev/null; then
                kill -9 $cvc5_pid 2>/dev/null || true
            fi
            if kill -0 $z3_pid 2>/dev/null; then
                kill -9 $z3_pid 2>/dev/null || true
            fi
            # Wait briefly for processes to terminate
            sleep 0.5
            # Mark as done if status files exist, otherwise assume timeout
            if [ ! -f "$cvc5_status" ]; then
                echo "124" > "$cvc5_status"
                cvc5_done=true
                cvc5_exit_code="124"
            fi
            if [ ! -f "$z3_status" ]; then
                echo "124" > "$z3_status"
                z3_done=true
                z3_exit_code="124"
            fi
            break
        fi
        
        # Check if cvc5 is done (status file exists means process finished)
        if [ "$cvc5_done" = false ] && [ -f "$cvc5_status" ]; then
            cvc5_done=true
            cvc5_exit_code=$(cat "$cvc5_status" 2>/dev/null | tr -d '[:space:]' || echo "")
            
            # Parse cvc5 result
            if [ -f "$cvc5_output" ]; then
                cvc5_result=$(grep -E "^(sat|unsat|unknown)$" "$cvc5_output" 2>/dev/null | tail -1 || echo "")
            fi
            
            # If cvc5 returned sat/unsat, kill z3 (suppress termination messages)
            if [ "$cvc5_result" = "sat" ] || [ "$cvc5_result" = "unsat" ]; then
                if kill -0 $z3_pid 2>/dev/null; then
                    # z3 is still running, kill it
                    { kill $z3_pid 2>/dev/null || true; } 2>/dev/null
                    z3_killed=true
                    # Wait briefly for z3 to terminate, but don't wait forever
                    timeout 2 bash -c "while kill -0 $z3_pid 2>/dev/null; do sleep 0.1; done" 2>/dev/null || true
                fi
                z3_done=true
                final_result="$cvc5_result"
                break
            fi
        fi
        
        # Check if z3 is done (status file exists means process finished)
        if [ "$z3_done" = false ] && [ -f "$z3_status" ]; then
            z3_done=true
            z3_exit_code=$(cat "$z3_status" 2>/dev/null | tr -d '[:space:]' || echo "")
            
            # Parse z3 result
            if [ -f "$z3_output" ]; then
                z3_result=$(grep -E "^(sat|unsat|unknown)$" "$z3_output" 2>/dev/null | tail -1 || echo "")
            fi
            
            # If z3 returned sat/unsat, kill cvc5 (suppress termination messages)
            if [ "$z3_result" = "sat" ] || [ "$z3_result" = "unsat" ]; then
                if kill -0 $cvc5_pid 2>/dev/null; then
                    # cvc5 is still running, kill it
                    { kill $cvc5_pid 2>/dev/null || true; } 2>/dev/null
                    cvc5_killed=true
                    # Wait briefly for cvc5 to terminate, but don't wait forever
                    timeout 2 bash -c "while kill -0 $cvc5_pid 2>/dev/null; do sleep 0.1; done" 2>/dev/null || true
                fi
                cvc5_done=true
                final_result="$z3_result"
                break
            fi
        fi
        
        # Also check if processes are still alive
        if [ "$cvc5_done" = false ] && ! kill -0 $cvc5_pid 2>/dev/null; then
            # Process died but status file might not exist yet, wait a bit
            sleep 0.2
            if [ -f "$cvc5_status" ]; then
                cvc5_done=true
                cvc5_exit_code=$(cat "$cvc5_status" 2>/dev/null | tr -d '[:space:]' || echo "")
                if [ -f "$cvc5_output" ]; then
                    cvc5_result=$(grep -E "^(sat|unsat|unknown)$" "$cvc5_output" 2>/dev/null | tail -1 || echo "")
                fi
            fi
        fi
        
        if [ "$z3_done" = false ] && ! kill -0 $z3_pid 2>/dev/null; then
            # Process died but status file might not exist yet, wait a bit
            sleep 0.2
            if [ -f "$z3_status" ]; then
                z3_done=true
                z3_exit_code=$(cat "$z3_status" 2>/dev/null | tr -d '[:space:]' || echo "")
                if [ -f "$z3_output" ]; then
                    z3_result=$(grep -E "^(sat|unsat|unknown)$" "$z3_output" 2>/dev/null | tail -1 || echo "")
                fi
            fi
        fi
        
        # If both are done (and no final result yet), break
        if [ "$cvc5_done" = true ] && [ "$z3_done" = true ]; then
            break
        fi
        
        # Small sleep to avoid busy waiting
        sleep 0.1
    done
    
    # Wait briefly for any remaining processes (with timeout, suppress all output)
    wait $cvc5_pid 2>/dev/null || true
    wait $z3_pid 2>/dev/null || true
    
    # Ensure we read exit codes if they weren't set
    if [ -z "$cvc5_exit_code" ] && [ -f "$cvc5_status" ]; then
        cvc5_exit_code=$(cat "$cvc5_status" | tr -d '[:space:]')
        cvc5_done=true
    fi
    if [ -z "$z3_exit_code" ] && [ -f "$z3_status" ]; then
        z3_exit_code=$(cat "$z3_status" | tr -d '[:space:]')
        z3_done=true
    fi
    
    # Parse results if not already parsed
    if [ -z "$cvc5_result" ] && [ -f "$cvc5_output" ]; then
        cvc5_result=$(grep -E "^(sat|unsat|unknown)$" "$cvc5_output" 2>/dev/null | tail -1 || echo "")
    fi
    if [ -z "$z3_result" ] && [ -f "$z3_output" ]; then
        z3_result=$(grep -E "^(sat|unsat|unknown)$" "$z3_output" 2>/dev/null | tail -1 || echo "")
    fi
    
    # Determine final result
    if [ -z "$final_result" ]; then
        if [ "$cvc5_result" = "sat" ] || [ "$cvc5_result" = "unsat" ]; then
            final_result="$cvc5_result"
        elif [ "$z3_result" = "sat" ] || [ "$z3_result" = "unsat" ]; then
            final_result="$z3_result"
        elif [ "$cvc5_result" = "unknown" ] || [ "$z3_result" = "unknown" ]; then
            final_result="unknown"
        else
            # Check for timeouts - normalize exit codes to integers
            cvc5_timeout=false
            z3_timeout=false
            cvc5_exit_int=$(echo "$cvc5_exit_code" | tr -d '[:space:]' | grep -E '^[0-9]+$' || echo "")
            z3_exit_int=$(echo "$z3_exit_code" | tr -d '[:space:]' | grep -E '^[0-9]+$' || echo "")
            
            if [ "$cvc5_exit_int" = "124" ] || [ "$cvc5_exit_int" = "137" ] || [ "$cvc5_exit_int" = "143" ]; then
                cvc5_timeout=true
            fi
            if [ "$z3_exit_int" = "124" ] || [ "$z3_exit_int" = "137" ] || [ "$z3_exit_int" = "143" ]; then
                z3_timeout=true
            fi
            
            # Only mark as timeout if both timeout
            if [ "$cvc5_timeout" = true ] && [ "$z3_timeout" = true ]; then
                final_result="timeout"
            else
                # One or both didn't timeout, but we have no sat/unsat/unknown result, so it's an error
                final_result="error"
            fi
        fi
    fi
    
    # Determine which solver found the result
    solver_used=""
    if [ "$cvc5_result" = "sat" ] || [ "$cvc5_result" = "unsat" ]; then
        solver_used="cvc5"
    elif [ "$z3_result" = "sat" ] || [ "$z3_result" = "unsat" ]; then
        solver_used="z3"
    fi
    
    # Process final result (restore stderr for echo commands)
    exec 2>&3  # Restore stderr for echo commands
    case "$final_result" in
        sat)
            echo -e "${RED}SAT${NC}${solver_used:+ (via $solver_used)}"
            sat_count=$((sat_count + 1))
            sat_files+=("$filename")
            echo "$filename: SAT${solver_used:+ (via $solver_used)}" >> "$RESULTS_FILE"
            if ! grep -Fxq "$filename" "$SAT_CACHE_FILE"; then echo "$filename" >> "$SAT_CACHE_FILE"; fi
            update_timestamp_cache "$filename" "$smt2_file"
            ;;
        unsat)
            echo -e "${GREEN}UNSAT${NC}${solver_used:+ (via $solver_used)}"
            unsat_count=$((unsat_count + 1))
            unsat_files+=("$filename")
            echo "$filename: UNSAT${solver_used:+ (via $solver_used)}" >> "$RESULTS_FILE"
            if ! grep -Fxq "$filename" "$CACHE_FILE"; then echo "$filename" >> "$CACHE_FILE"; fi
            update_timestamp_cache "$filename" "$smt2_file"
            ;;
        unknown)
            echo -e "${YELLOW}UNKNOWN${NC}"
            unknown_count=$((unknown_count + 1))
            unknown_files+=("$filename")
            echo "$filename: UNKNOWN" >> "$RESULTS_FILE"
            echo "  cvc5: ${cvc5_result:-no result} (exit ${cvc5_exit_code:-unknown})" >> "$RESULTS_FILE"
            echo "  z3: ${z3_result:-no result} (exit ${z3_exit_code:-unknown})" >> "$RESULTS_FILE"
            # Update timestamp even for unknown/timeout/error so we don't keep retrying unchanged files
            update_timestamp_cache "$filename" "$smt2_file"
            ;;
        timeout)
            echo -e "${YELLOW}TIMEOUT${NC}"
            timeout_count=$((timeout_count + 1))
            timeout_files+=("$filename")
            echo "$filename: TIMEOUT" >> "$RESULTS_FILE"
            echo "  cvc5: ${cvc5_result:-no result} (exit ${cvc5_exit_code:-unknown})" >> "$RESULTS_FILE"
            echo "  z3: ${z3_result:-no result} (exit ${z3_exit_code:-unknown})" >> "$RESULTS_FILE"
            # Update timestamp even for unknown/timeout/error so we don't keep retrying unchanged files
            update_timestamp_cache "$filename" "$smt2_file"
            ;;
        error)
            echo -e "${RED}ERROR${NC}"
            error_count=$((error_count + 1))
            error_files+=("$filename")
            echo "$filename: ERROR" >> "$RESULTS_FILE"
            echo "  cvc5: ${cvc5_result:-no result} (exit ${cvc5_exit_code:-unknown})" >> "$RESULTS_FILE"
            echo "  z3: ${z3_result:-no result} (exit ${z3_exit_code:-unknown})" >> "$RESULTS_FILE"
            if [ -f "$cvc5_output" ]; then
                echo "  cvc5 output: $(cat "$cvc5_output")" >> "$RESULTS_FILE"
            fi
            if [ -f "$z3_output" ]; then
                echo "  z3 output: $(cat "$z3_output")" >> "$RESULTS_FILE"
            fi
            # Update timestamp even for unknown/timeout/error so we don't keep retrying unchanged files
            update_timestamp_cache "$filename" "$smt2_file"
            ;;
    esac
    exec 2>/dev/null  # Redirect stderr again to suppress job control messages
    
    # Clean up temporary files
    rm -f "$cvc5_output" "$z3_output" "$cvc5_status" "$z3_status"
done

# Restore stderr after the loop
exec 2>&3

# Clean up temp files
rm -f /tmp/cvc5_output.txt /tmp/z3_output.txt

echo ""
echo "=========================================="
echo -e "${BLUE}Benchmark completed!${NC}"
echo ""

# Calculate totals including cached files
total_with_cached=$((total_files + cached_sat_count + cached_unsat_count))
total_unsat=$((unsat_count + cached_unsat_count))
total_sat=$((sat_count + cached_sat_count))

# Calculate success rates
if [ $total_files -gt 0 ]; then
    success_rate_this_run=$(( (unsat_count * 100) / total_files ))
else
    success_rate_this_run=0
fi
if [ $total_with_cached -gt 0 ]; then
    success_rate_overall=$(( (total_unsat * 100) / total_with_cached ))
else
    success_rate_overall=0
fi

# Generate summary
cat > "$SUMMARY_FILE" << EOF
Parallel cvc5/z3 Benchmark Summary - $(date)
==========================================

Total files processed: $total_files
Cached files (skipped): $((cached_sat_count + cached_unsat_count))
  - Cached UNSAT: $cached_unsat_count
  - Cached SAT: $cached_sat_count
Total files (including cached): $total_with_cached

Results breakdown (processed in this run):
- UNSAT (success): $unsat_count files
- SAT (fail): $sat_count files  
- Timeout: $timeout_count files
- Error: $error_count files
- Unknown: $unknown_count files

Overall results (including cached):
- UNSAT (success): $total_unsat files
- SAT (fail): $total_sat files

Success rate (this run): $success_rate_this_run%
Success rate (overall): $success_rate_overall%

==========================================

UNSAT files ($unsat_count):
$(printf '%s\n' "${unsat_files[@]}")

SAT files ($sat_count):
$(printf '%s\n' "${sat_files[@]}")

Timeout files ($timeout_count):
$(printf '%s\n' "${timeout_files[@]}")

Error files ($error_count):
$(printf '%s\n' "${error_files[@]}")

Unknown files ($unknown_count):
$(printf '%s\n' "${unknown_files[@]}")

Cached UNSAT files ($cached_unsat_count):
$(printf '%s\n' "${cached_unsat_files[@]}")

Cached SAT files ($cached_sat_count):
$(printf '%s\n' "${cached_sat_files[@]}")
EOF

# Display summary
echo -e "${GREEN}UNSAT (success): $unsat_count files${NC}"
echo -e "${RED}SAT (fail): $sat_count files${NC}"
echo -e "${YELLOW}Timeout: $timeout_count files${NC}"
echo -e "${RED}Error: $error_count files${NC}"
echo -e "${YELLOW}Unknown: $unknown_count files${NC}"
if [ $((cached_sat_count + cached_unsat_count)) -gt 0 ]; then
    echo -e "${BLUE}Cached files (skipped): $((cached_sat_count + cached_unsat_count)) (UNSAT: $cached_unsat_count, SAT: $cached_sat_count)${NC}"
fi
echo ""
if [ $total_files -gt 0 ]; then
    echo -e "${BLUE}Success rate (this run): $(( (unsat_count * 100) / total_files ))%${NC}"
fi
if [ $total_with_cached -gt 0 ]; then
    echo -e "${BLUE}Success rate (overall): $(( (total_unsat * 100) / total_with_cached ))%${NC}"
fi
echo ""
echo "Detailed results saved to: $RESULTS_FILE"
echo "Summary saved to: $SUMMARY_FILE"

# Show detailed breakdown if there are failures
if [ $sat_count -gt 0 ] || [ $timeout_count -gt 0 ] || [ $error_count -gt 0 ] || [ $unknown_count -gt 0 ]; then
    echo ""
    echo "=========================================="
    echo -e "${RED}Files that failed (SAT):${NC}"
    for file in "${sat_files[@]}"; do
        echo "  - $file"
    done
    
    if [ $timeout_count -gt 0 ]; then
        echo ""
        echo -e "${YELLOW}Files that timed out:${NC}"
        for file in "${timeout_files[@]}"; do
            echo "  - $file"
        done
    fi
    
    if [ $error_count -gt 0 ]; then
        echo ""
        echo -e "${RED}Files with errors:${NC}"
        for file in "${error_files[@]}"; do
            echo "  - $file"
        done
    fi
    
    if [ $unknown_count -gt 0 ]; then
        echo ""
        echo -e "${YELLOW}Files with unknown results:${NC}"
        for file in "${unknown_files[@]}"; do
            echo "  - $file"
        done
    fi
fi

echo ""
echo -e "${GREEN}Files that succeeded (UNSAT):${NC}"
for file in "${unsat_files[@]}"; do
    echo "  - $file"
done

