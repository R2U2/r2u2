#!/bin/bash

# Script to process .equiv files and generate .smt2 files
# Tries to prove each with a short timeout of 1 second.
# Usage: ./process_equiv_files.sh

# Set the base directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
MLTL_DIR="$SCRIPT_DIR/equiv"
SMT2_DIR="$SCRIPT_DIR/smt2"

# Create the smt2 directory if it doesn't exist
mkdir -p "$SMT2_DIR"

# Check if the mltl directory exists
if [ ! -d "$MLTL_DIR" ]; then
    echo "Error: Directory $MLTL_DIR does not exist"
    exit 1
fi

# Check if the c2po.py script exists
C2PO_SCRIPT="$SCRIPT_DIR/../c2po.py"
if [ ! -f "$C2PO_SCRIPT" ]; then
    echo "Error: $C2PO_SCRIPT does not exist"
    exit 1
fi

# Counter for processed files
processed=0
total=0

# Count total files first
for file in "$MLTL_DIR"/*.equiv; do
    if [ -f "$file" ]; then
        ((total++))
    fi
done

echo "Found $total .equiv files to process"
echo "Processing files..."

# Process each .equiv file
for file in "$MLTL_DIR"/*.equiv; do
    if [ -f "$file" ]; then
        # Extract the base filename without extension
        basename=$(basename "$file" .equiv)
        
        # Define output file path
        output_file="$SMT2_DIR/${basename}.smt2"
        
        echo "Processing: $basename.equiv -> $basename.smt2"
        
        # Run the Python command and capture stderr to determine failure reasons
        command_output=$({ python3 "$C2PO_SCRIPT" --smt-max-time 1 "$file" >"$output_file"; } 2>&1)
        exit_code=$?
        if [ $exit_code -eq 0 ]; then
            ((processed++))
            echo "  ✓ Success"
        else
            failure_reason="Failed"
            if [[ "$command_output" == *"Equivalence check unknown"* ]]; then
                failure_reason="Unknown/Timeout"
            elif [[ "$command_output" == *"Equivalence check failed"* ]]; then
                failure_reason="Equivalence check failed"
            fi
            echo "  ✗ $failure_reason"
        fi
    fi
done

echo ""
echo "Processing complete!"
echo "Successfully processed: $processed/$total files"
echo "Output files saved to: $SMT2_DIR"
