#!/usr/bin/env python3
"""
Generate .mltl files for all formulas in patterns.md with different bound combinations.

Generated on 2025-12-22 by Cursor AI.
"""

import os
import re

# Bound combinations: (t_l, t_u, M)
BOUND_COMBINATIONS = [
    (0, 10, 10),
    (0, 100, 100),
    (0, 1000, 1000),
    (10, 100, 100),
    (100, 1000, 1000),
]

def expand_chain(formula: str, chain_length: int, start_var: int = 5) -> str:
    """
    Expand Ch(1) to a chain of length chain_length.
    Example: Ch(1) of length 3 -> F[0,t_u] (a5 & F[0,t_u] (a6 & F[0,t_u] (a7)))
    """
    if chain_length == 1:
        # Ch(1) of length 1 is just F[0, t_u] a{start_var}
        return formula.replace("Ch(1)", f"F[0, t_u] a{start_var}")
    
    # Build chain from inside out
    # For length 3: F[0,t_u] a7, then F[0,t_u] (a6 & F[0,t_u] a7), then F[0,t_u] (a5 & F[0,t_u] (a6 & F[0,t_u] a7))
    chain = f"(F[0, t_u] a{start_var + chain_length - 1})"
    for i in range(chain_length - 2, -1, -1):
        chain = f"F[0, t_u] (a{start_var + i} & {chain})"
    
    return formula.replace("Ch(1)", chain)

def substitute_bounds(formula: str, t_l: int, t_u: int, M: int) -> str:
    """Substitute t_l, t_u, M, and t_gap in the formula."""
    t_gap = t_u - t_l
    formula = formula.replace("t_l", str(t_l))
    formula = formula.replace("t_u", str(t_u))
    formula = formula.replace("t_gap", str(t_gap))
    # Replace M only when it's not part of a variable name
    # Use word boundary to avoid replacing "M" in variable names
    formula = re.sub(r'\bM\b', str(M), formula)
    return formula

def sanitize_filename(name: str) -> str:
    """Convert a formula name to a valid filename."""
    # Replace spaces and special chars with underscores
    name = re.sub(r'[^\w\s-]', '', name)
    name = re.sub(r'[-\s]+', '_', name)
    return name.lower()

def extract_formulas():
    """Extract all formulas from patterns.md."""
    formulas = []
    
    with open("patterns.md", "r") as f:
        lines = f.readlines()
    
    current_section_name = None
    
    # Patterns
    subsection_pattern = re.compile(r'^#### (\d+)\. (.+)$')
    formula_pattern = re.compile(r'\* \*\*([^*]+)\*\*:\s*`([^`]+)`')
    
    for line in lines:
        line = line.rstrip()
        
        # Check for subsection header (e.g., "#### 1. Absence")
        subsection_match = subsection_pattern.match(line)
        if subsection_match:
            current_section_name = sanitize_filename(subsection_match.group(2))
            continue
        
        # Check for formula
        formula_match = formula_pattern.match(line)
        if formula_match:
            pattern_name_raw = formula_match.group(1).strip()
            formula = formula_match.group(2).strip()
            
            # Simplify pattern name - map to standard names
            pattern_name_raw_lower = pattern_name_raw.lower()
            if "globally" in pattern_name_raw_lower:
                pattern_name = "globally"
            elif "before" in pattern_name_raw_lower:
                pattern_name = "before"
            elif "after" in pattern_name_raw_lower and "until" in pattern_name_raw_lower:
                pattern_name = "after_until"
            elif "between" in pattern_name_raw_lower:
                pattern_name = "between"
            elif "after" in pattern_name_raw_lower:
                pattern_name = "after"
            else:
                # Fallback: sanitize the original name
                pattern_name = sanitize_filename(pattern_name_raw)
            
            # Build simplified name: {section_name}_{pattern_name}
            if current_section_name:
                full_name = f"{current_section_name}_{pattern_name}"
            else:
                full_name = pattern_name
            
            formulas.append({
                'name': full_name,
                'formula': formula,
                'has_chain': 'Ch(1)' in formula
            })
    
    return formulas

def main():
    """Generate all .mltl files."""
    formulas = extract_formulas()
    
    print(f"Found {len(formulas)} formulas")
    
    # Create directories for each bound combination
    for t_l, t_u, M in BOUND_COMBINATIONS:
        dir_name = f"{t_l}_{t_u}_{M}"
        os.makedirs(dir_name, exist_ok=True)
        print(f"Created directory: {dir_name}")
    
    # Generate files
    for formula_info in formulas:
        formula = formula_info['formula']
        name = formula_info['name']
        has_chain = formula_info['has_chain']
        
        for t_l, t_u, M in BOUND_COMBINATIONS:
            dir_name = f"{t_l}_{t_u}_{M}"
            
            if has_chain:
                # Generate versions with chain lengths 1-5
                for chain_len in range(1, 6):
                    expanded_formula = expand_chain(formula, chain_len)
                    substituted = substitute_bounds(expanded_formula, t_l, t_u, M)
                    
                    filename = f"{sanitize_filename(name)}_chain{chain_len}.mltl"
                    filepath = os.path.join(dir_name, filename)
                    
                    with open(filepath, 'w') as f:
                        f.write(substituted + '\n')
            else:
                # Regular formula, no chain expansion needed
                substituted = substitute_bounds(formula, t_l, t_u, M)
                
                filename = f"{sanitize_filename(name)}.mltl"
                filepath = os.path.join(dir_name, filename)
                
                with open(filepath, 'w') as f:
                    f.write(substituted + '\n')
    
    print(f"Generated .mltl files for {len(formulas)} formulas")

if __name__ == "__main__":
    main()

