#!/usr/bin/env python3
"""
Script to convert formulas in benchmarks/boeing-wbs/properties/properties_X.xml 
to C2PO files. Each XML file gets its own directory of .c2po files, with each 
formula having its own file.

This file was generated on 12/31/2025 by Cursor AI.
"""

import re
import xml.etree.ElementTree as ET
from pathlib import Path


def extract_formulas_from_xml(xml_path: Path):
    """Extract all formulas from an XML file."""
    tree = ET.parse(xml_path)
    root = tree.getroot()
    
    formulas = []
    for property_elem in root.findall('property'):
        name = property_elem.find('name')
        index = property_elem.find('index')
        formula = property_elem.find('formula')
        
        if name is not None and formula is not None:
            formulas.append({
                'name': name.text or f"property_{index.text if index is not None else 'unknown'}",
                'index': index.text if index is not None else '0',
                'formula': formula.text.strip() if formula.text else ''
            })
    
    return formulas


def convert_true_false(formula: str) -> str:
    """Convert TRUE to true and FALSE to false."""
    # Use word boundaries to avoid matching substrings
    formula = re.sub(r'\bTRUE\b', 'true', formula)
    formula = re.sub(r'\bFALSE\b', 'false', formula)
    return formula


def convert_constant_integers_to_propositions(formula: str) -> tuple[str, dict[str, str]]:
    """
    Convert constant integers to propositions.
    Returns (converted_formula, constant_map) where constant_map maps 
    integer constants to proposition names.
    """
    constant_map = {}
    prop_counter = 0
    
    def replace_integer(match):
        nonlocal prop_counter
        integer_str = match.group(0)
        integer_val = int(integer_str)
        
        # Create a unique key for this integer
        key = f"__int{integer_val}__"
        if key not in constant_map:
            prop_name = f"__int{prop_counter}__"
            constant_map[key] = prop_name
            prop_counter += 1
        return constant_map[key]
    
    # Match integers that are not part of intervals [0, 1000] or other contexts
    # We need to be careful not to match numbers in intervals
    # Process character by character to avoid matching in intervals
    converted = []
    i = 0
    while i < len(formula):
        # Check if we're in an interval [ ... ]
        if formula[i] == '[':
            # Find matching ]
            bracket_depth = 1
            j = i + 1
            while j < len(formula) and bracket_depth > 0:
                if formula[j] == '[':
                    bracket_depth += 1
                elif formula[j] == ']':
                    bracket_depth -= 1
                j += 1
            # Copy the interval as-is
            converted.append(formula[i:j])
            i = j
        elif formula[i].isdigit():
            # Found a digit, check if it's part of an interval or standalone
            # Look backwards to see if we're after [ or ,
            is_in_interval = False
            if i > 0:
                # Check if we're inside brackets
                bracket_count = 0
                for k in range(i - 1, -1, -1):
                    if formula[k] == ']':
                        bracket_count += 1
                    elif formula[k] == '[':
                        bracket_count -= 1
                        if bracket_count < 0:
                            is_in_interval = True
                            break
                    elif bracket_count == 0 and formula[k] not in ' \t\n,':
                        break
            
            if not is_in_interval:
                # Extract the full number
                num_start = i
                while i < len(formula) and formula[i].isdigit():
                    i += 1
                integer_str = formula[num_start:i]
                integer_val = int(integer_str)
                
                key = f"__int{integer_val}__"
                if key not in constant_map:
                    prop_name = f"__int{prop_counter}__"
                    constant_map[key] = prop_name
                    prop_counter += 1
                converted.append(constant_map[key])
            else:
                converted.append(formula[i])
                i += 1
        else:
            converted.append(formula[i])
            i += 1
    
    return ''.join(converted), constant_map


def convert_addition_to_proposition(formula: str) -> tuple[str, dict[str, str]]:
    """
    Convert addition expressions (f1 + f2) to propositions.
    Returns (converted_formula, addition_map) where addition_map maps 
    addition expressions to proposition names.
    """
    addition_map = {}
    prop_counter = 0
    
    def replace_addition(match):
        nonlocal prop_counter
        left = match.group(1).strip()
        right = match.group(2).strip()
        addition_expr = f"{left} + {right}"
        
        if addition_expr not in addition_map:
            prop_name = f"__add{prop_counter}__"
            addition_map[addition_expr] = prop_name
            prop_counter += 1
        return addition_map[addition_expr]
    
    # Process additions from right to left to avoid position issues
    # Find all '+' that are not part of -> or =
    converted = formula
    max_iterations = 1000
    iteration = 0
    
    while iteration < max_iterations:
        iteration += 1
        # Find the rightmost + that's not part of -> or =
        plus_pos = -1
        for i in range(len(converted) - 1, 0, -1):
            if converted[i] == '+' and (i == 0 or converted[i-1] not in '-='):
                plus_pos = i
                break
        
        if plus_pos == -1:
            break
        
        # Find left operand (scan backwards)
        left_end = plus_pos
        paren_depth = 0
        bracket_depth = 0
        
        i = plus_pos - 1
        while i >= 0:
            char = converted[i]
            if char == ')':
                paren_depth += 1
            elif char == '(':
                paren_depth -= 1
                if paren_depth < 0:
                    break
            elif char == ']':
                bracket_depth += 1
            elif char == '[':
                bracket_depth -= 1
            elif paren_depth == 0 and bracket_depth == 0:
                if char in ',;=&|!':
                    break
            left_end = i
            i -= 1
        
        left = converted[left_end:plus_pos].strip()
        
        # Find right operand (scan forwards)
        right_start = plus_pos + 1
        paren_depth = 0
        bracket_depth = 0
        
        # Skip whitespace
        while right_start < len(converted) and converted[right_start] in ' \t\n':
            right_start += 1
        
        j = right_start
        while j < len(converted):
            char = converted[j]
            if char == '(':
                paren_depth += 1
            elif char == ')':
                paren_depth -= 1
                if paren_depth < 0:
                    break
            elif char == '[':
                bracket_depth += 1
            elif char == ']':
                bracket_depth -= 1
            elif paren_depth == 0 and bracket_depth == 0:
                if char in ',;=&|!+':
                    break
            j += 1
        
        right = converted[right_start:j].strip()
        
        if left and right:
            addition_expr = f"{left} + {right}"
            if addition_expr not in addition_map:
                prop_name = f"__add{prop_counter}__"
                addition_map[addition_expr] = prop_name
                prop_counter += 1
            
            # Replace this addition
            replacement = addition_map[addition_expr]
            converted = converted[:left_end] + replacement + converted[j:]
        else:
            # Can't parse, skip this +
            break
    
    return converted, addition_map


def convert_case_statements(formula: str) -> str:
    """
    Convert case statements to conjunctions of implications.
    Pattern: case ... condition : value; ... TRUE : default; esac
    Converts to: (condition -> value) & ... & (true -> default)
    """
    def convert_single_case(case_content: str) -> str:
        """Convert a single case statement content to implications."""
        # Split by semicolons, but be careful with nested parentheses
        cases = []
        current_case = ""
        paren_depth = 0
        bracket_depth = 0
        
        i = 0
        while i < len(case_content):
            char = case_content[i]
            if char == '(':
                paren_depth += 1
                current_case += char
            elif char == ')':
                paren_depth -= 1
                current_case += char
            elif char == '[':
                bracket_depth += 1
                current_case += char
            elif char == ']':
                bracket_depth -= 1
                current_case += char
            elif char == ';' and paren_depth == 0 and bracket_depth == 0:
                if current_case.strip():
                    cases.append(current_case.strip())
                current_case = ""
            else:
                current_case += char
            i += 1
        
        # Add the last case if any
        if current_case.strip():
            cases.append(current_case.strip())
        
        # Convert each case to an implication
        implications = []
        for case in cases:
            if ':' in case:
                # Find the first colon that's not inside parentheses
                colon_pos = -1
                depth = 0
                for idx, ch in enumerate(case):
                    if ch == '(':
                        depth += 1
                    elif ch == ')':
                        depth -= 1
                    elif ch == ':' and depth == 0:
                        colon_pos = idx
                        break
                
                if colon_pos >= 0:
                    condition = case[:colon_pos].strip()
                    value = case[colon_pos+1:].strip()
                    implications.append(f"({condition} -> {value})")
        
        # Join with &
        if implications:
            return " & ".join(implications)
        return case_content
    
    # Find and replace case...esac blocks
    # Handle nested cases by tracking depth
    result = []
    i = 0
    while i < len(formula):
        # Check for 'case' (case-insensitive, word boundary)
        remaining = formula[i:].lower()
        if remaining.startswith('case') and (i == 0 or not (formula[i-1].isalnum() or formula[i-1] == '_')):
            # Find matching 'esac'
            depth = 1
            j = i + 4
            start = i
            
            # Skip whitespace after 'case'
            while j < len(formula) and formula[j] in ' \t\n':
                j += 1
            
            while j < len(formula) and depth > 0:
                remaining_text = formula[j:].lower()
                if remaining_text.startswith('case') and (j == 0 or not (formula[j-1].isalnum() or formula[j-1] == '_')):
                    depth += 1
                    j += 4
                elif remaining_text.startswith('esac') and (j == 0 or not (formula[j-1].isalnum() or formula[j-1] == '_')):
                    depth -= 1
                    if depth == 0:
                        # Found matching esac
                        case_content = formula[start+4:j].strip()
                        converted = convert_single_case(case_content)
                        result.append(f"({converted})")
                        i = j + 4
                        break
                    j += 4
                else:
                    j += 1
            else:
                # No matching esac found, keep original
                result.append(formula[i])
                i += 1
        else:
            result.append(formula[i])
            i += 1
    
    return ''.join(result)


def convert_equality_to_proposition(formula: str) -> tuple[str, dict[str, str]]:
    """
    Convert equality expressions (f1 = f2) to propositions.
    Returns (converted_formula, equality_map) where equality_map maps 
    equality expressions to proposition names.
    Handles both simple identifiers and parenthesized expressions.
    """
    equality_map = {}
    prop_counter = 0
    
    def replace_equality(left: str, right: str) -> str:
        nonlocal prop_counter
        left = left.strip()
        right = right.strip()
        equality_expr = f"{left} = {right}"
        if equality_expr not in equality_map:
            prop_name = f"__eq{prop_counter}__"
            equality_map[equality_expr] = prop_name
            prop_counter += 1
        return equality_map[equality_expr]
    
    # Process formula to find equality expressions from right to left
    # This avoids position issues when replacing
    converted = formula
    max_iterations = 1000
    iteration = 0
    
    while iteration < max_iterations:
        iteration += 1
        # Find the rightmost = that's not part of -> or <= or >=
        eq_pos = -1
        for i in range(len(converted) - 1, 0, -1):
            if converted[i] == '=' and (i == 0 or converted[i-1] not in '-<>'):
                eq_pos = i
                break
        
        if eq_pos == -1:
            break
        
        # Find left operand (scan backwards)
        left_start = eq_pos
        paren_depth = 0
        bracket_depth = 0
        
        j = eq_pos - 1
        while j >= 0:
            char = converted[j]
            if char == ')':
                paren_depth += 1
            elif char == '(':
                paren_depth -= 1
                if paren_depth < 0:
                    # Found opening paren, start after it
                    left_start = j + 1
                    break
            elif char == ']':
                bracket_depth += 1
            elif char == '[':
                bracket_depth -= 1
            elif paren_depth == 0 and bracket_depth == 0:
                if char in ',;=&|!+-><':
                    break
            left_start = j
            j -= 1
        
        left = converted[left_start:eq_pos].strip()
        
        # Find right operand (scan forwards)
        right_start = eq_pos + 1
        paren_depth = 0
        bracket_depth = 0
        
        # Skip whitespace
        while right_start < len(converted) and converted[right_start] in ' \t\n':
            right_start += 1
        
        k = right_start
        while k < len(converted):
            char = converted[k]
            if char == '(':
                paren_depth += 1
            elif char == ')':
                paren_depth -= 1
                if paren_depth < 0:
                    # Found closing paren, stop before it
                    break
            elif char == '[':
                bracket_depth += 1
            elif char == ']':
                bracket_depth -= 1
            elif paren_depth == 0 and bracket_depth == 0:
                if char in ',;=&|!+-><':
                    break
            k += 1
        
        right = converted[right_start:k].strip()
        
        if left and right:
            # Replace with proposition
            replacement = replace_equality(left, right)
            converted = converted[:left_start] + replacement + converted[k:]
        else:
            # Can't parse, remove this = and continue
            converted = converted[:eq_pos] + converted[eq_pos+1:]
    
    return converted, equality_map


def normalize_propositions(formula: str, equality_map: dict[str, str]) -> tuple[str, dict[str, str]]:
    """
    Map all atomic propositions to aN format where N is a number >= 0.
    Returns (converted_formula, prop_mapping) where prop_mapping maps 
    original propositions to aN format.
    """
    prop_mapping = {}
    prop_counter = 0
    
    # First, add equality propositions to mapping
    for eq_expr, prop_name in equality_map.items():
        prop_mapping[prop_name] = f"a{prop_counter}"
        prop_counter += 1
    
    # Pattern to match atomic propositions:
    # - Identifiers: word characters, dots, underscores
    # - Exclude already mapped propositions (__eqN__)
    # - Exclude operators: G, F, H, O, U, R, S, T, true, false
    # - Exclude numbers
    # - Exclude comparison operators: >, <, >=, <=
    
    # Keywords to exclude (only actual MLTL keywords)
    keywords = {'G', 'F', 'H', 'O', 'U', 'R', 'S', 'T', 'true', 'false'}
    
    # Pattern to match identifiers (propositions)
    # Match: word starting with letter/underscore, followed by letters, digits, dots, underscores
    # But exclude if it's a keyword or already mapped
    identifier_pattern = r'\b([a-zA-Z_][a-zA-Z0-9_.]*)\b'
    
    def replace_proposition(match):
        nonlocal prop_counter
        prop = match.group(1)
        
        # Skip if it's a keyword
        if prop in keywords:
            return prop
        
        # Skip if it's already mapped
        if prop in prop_mapping:
            return prop_mapping[prop]
        
        # Skip if it's a number
        if prop.isdigit():
            return prop
        
        # Skip if it's already in aN format
        if re.match(r'^a[0-9]+$', prop):
            return prop
        
        # Skip if it's a special prop placeholder (__eqN__, __cmpN__)
        if prop.startswith('__') and prop.endswith('__'):
            # Already handled in all_special_props
            if prop not in prop_mapping:
                prop_mapping[prop] = f"a{prop_counter}"
                prop_counter += 1
            return prop_mapping[prop]
        
        # Map to aN
        prop_mapping[prop] = f"a{prop_counter}"
        prop_counter += 1
        return prop_mapping[prop]
    
    # Replace all identifiers
    converted = re.sub(identifier_pattern, replace_proposition, formula)
    
    return converted, prop_mapping


def convert_ltl_to_mltl(formula: str, interval: str = "[0, 1000]") -> str:
    """
    Convert LTL operators to MLTL format by adding intervals.
    LTL operators without intervals need intervals added.
    Also replaces existing intervals with the specified interval.
    
    Args:
        formula: The formula to convert
        interval: The interval to use (default: "[0, 1000]")
    """
    # First, replace all existing intervals with the target interval
    # Pattern: [number, number] or [number,number]
    formula = re.sub(r'\[\s*\d+\s*,\s*\d+\s*\]', interval, formula)
    
    # Pattern to match LTL operators without intervals
    # G, F, H, O need intervals
    # U, R, S, T need intervals
    
    # Replace G (global) without interval
    formula = re.sub(r'\bG\s*(?![\[\(])', f'G{interval} ', formula)
    
    # Replace F (future) without interval
    formula = re.sub(r'\bF\s*(?![\[\(])', f'F{interval} ', formula)
    
    # Replace H (historical) without interval
    formula = re.sub(r'\bH\s*(?![\[\(])', f'H{interval} ', formula)
    
    # Replace O (once) without interval
    formula = re.sub(r'\bO\s*(?![\[\(])', f'O{interval} ', formula)
    
    # For U, R, S, T - these are binary operators, need to handle carefully
    # Pattern: expr U expr, expr R expr, etc.
    # We'll add interval before the second operand
    
    # U (until) - pattern: something U something
    # Need to be careful with parentheses
    def add_interval_to_binary_op(match):
        op = match.group(1)
        return f'{op}{interval} '
    
    # Replace U, R, S, T without intervals (they appear between two expressions)
    # This is tricky because we need to parse the structure
    # For now, we'll use a simpler approach: replace " U ", " R ", etc.
    formula = re.sub(r'\s+U\s+(?![\[\(])', f' U{interval} ', formula)
    formula = re.sub(r'\s+R\s+(?![\[\(])', f' R{interval} ', formula)
    formula = re.sub(r'\s+S\s+(?![\[\(])', f' S{interval} ', formula)
    formula = re.sub(r'\s+T\s+(?![\[\(])', f' T{interval} ', formula)
    
    # Clean up extra spaces
    formula = re.sub(r'\s+', ' ', formula)
    
    return formula


def convert_comparison_operators(formula: str) -> tuple[str, dict[str, str]]:
    """
    Convert comparison operators (>, <, >=, <=) to propositions.
    Returns (converted_formula, comparison_map).
    Handles both simple identifiers and parenthesized expressions.
    """
    comparison_map = {}
    prop_counter = 0
    
    def replace_comparison(left: str, op: str, right: str) -> str:
        nonlocal prop_counter
        left = left.strip()
        right = right.strip()
        comparison_expr = f"{left} {op} {right}"
        
        if comparison_expr not in comparison_map:
            prop_name = f"__cmp{prop_counter}__"
            comparison_map[comparison_expr] = prop_name
            prop_counter += 1
        return comparison_map[comparison_expr]
    
    # Process formula to find comparison expressions from right to left
    # This avoids position issues when replacing
    converted = formula
    max_iterations = 1000
    iteration = 0
    
    while iteration < max_iterations:
        iteration += 1
        # Find the rightmost > or < that's not part of -> or <= or >= or <->
        comp_pos = -1
        comp_op = None
        for i in range(len(converted) - 1, 0, -1):
            if converted[i] in '><':
                # Check if it's part of -> (previous char is -)
                if i > 0 and converted[i-1] == '-' and (i == 1 or converted[i-2] != '<'):
                    continue  # Part of ->
                # Check if it's part of <-> (current is <, next is -, or current is >, prev is - and prev-prev is <)
                if converted[i] == '<' and i < len(converted) - 2 and converted[i+1] == '-' and converted[i+2] == '>':
                    continue  # Part of <->
                if converted[i] == '>' and i > 1 and converted[i-1] == '-' and converted[i-2] == '<':
                    continue  # Part of <->
                # Check if it's >= or <=
                if i < len(converted) - 1 and converted[i+1] == '=':
                    comp_op = converted[i:i+2]
                else:
                    comp_op = converted[i]
                comp_pos = i
                break
        
        if comp_pos == -1:
            break
        
        # Find left operand (scan backwards)
        left_start = comp_pos
        paren_depth = 0
        bracket_depth = 0
        
        j = comp_pos - 1
        while j >= 0:
            char = converted[j]
            if char == ')':
                paren_depth += 1
            elif char == '(':
                paren_depth -= 1
                if paren_depth < 0:
                    # Found opening paren, start after it
                    left_start = j + 1
                    break
            elif char == ']':
                bracket_depth += 1
            elif char == '[':
                bracket_depth -= 1
            elif paren_depth == 0 and bracket_depth == 0:
                if char in ',;=&|!+-><':
                    break
            left_start = j
            j -= 1
        
        left = converted[left_start:comp_pos].strip()
        
        # Find right operand (scan forwards)
        right_start = comp_pos + len(comp_op)
        paren_depth = 0
        bracket_depth = 0
        
        # Skip whitespace
        while right_start < len(converted) and converted[right_start] in ' \t\n':
            right_start += 1
        
        k = right_start
        while k < len(converted):
            char = converted[k]
            if char == '(':
                paren_depth += 1
            elif char == ')':
                paren_depth -= 1
                if paren_depth < 0:
                    # Found closing paren, stop before it
                    break
            elif char == '[':
                bracket_depth += 1
            elif char == ']':
                bracket_depth -= 1
            elif paren_depth == 0 and bracket_depth == 0:
                if char in ',;=&|!+-><':
                    break
            k += 1
        
        right = converted[right_start:k].strip()
        
        if left and right:
            # Replace with proposition
            replacement = replace_comparison(left, comp_op, right)
            converted = converted[:left_start] + replacement + converted[k:]
        else:
            # Can't parse, skip this operator
            break
    
    return converted, comparison_map


def sanitize_filename(name: str) -> str:
    """Convert a property name to a valid filename."""
    # Replace invalid characters
    name = re.sub(r'[<>:"/\\|?*]', '_', name)
    # Replace dots and spaces with underscores
    name = re.sub(r'[.\s]+', '_', name)
    # Remove leading/trailing underscores
    name = name.strip('_')
    return name


def convert_formula_to_mltl(formula: str, interval: str = "[0, 1000]") -> str:
    """
    Convert a single LTL formula to MLTL format.
    
    Args:
        formula: The LTL formula to convert
        interval: The interval to use for temporal operators (default: "[0, 1000]")
    """
    # Step 1: Convert TRUE/FALSE to true/false (early, before other conversions)
    formula = convert_true_false(formula)
    
    # Step 2: Convert case statements to conjunctions of implications
    formula = convert_case_statements(formula)
    
    # Step 3: Convert comparison operators to propositions (before integer conversion, 
    #         since comparisons may contain integers)
    formula, comparison_map = convert_comparison_operators(formula)
    
    # Step 4: Convert constant integers to propositions (after comparisons, 
    #         since comparisons already handled their integers)
    formula, constant_map = convert_constant_integers_to_propositions(formula)
    
    # Step 5: Convert addition operations to propositions
    formula, addition_map = convert_addition_to_proposition(formula)
    
    # Step 6: Convert equality expressions to propositions
    formula, equality_map = convert_equality_to_proposition(formula)
    
    # Step 6.5: Convert comparison operators again (in case case conversion created new ones)
    formula, comparison_map2 = convert_comparison_operators(formula)
    comparison_map.update(comparison_map2)
    
    # Step 7: Merge all special props for normalization
    all_special_props = {**equality_map, **comparison_map, **addition_map, **constant_map}
    
    # Step 8: Normalize all propositions to aN format
    formula, prop_mapping = normalize_propositions(formula, all_special_props)
    
    # Step 8.5: Convert comparison operators one more time (in case normalization created new ones)
    formula, comparison_map3 = convert_comparison_operators(formula)
    # Update the comparison map, but we need to re-normalize if new comparisons were added
    if comparison_map3:
        # Re-normalize to convert new comparison propositions
        temp_special_props = {**all_special_props, **comparison_map3}
        formula, prop_mapping2 = normalize_propositions(formula, temp_special_props)
        prop_mapping.update(prop_mapping2)
    
    # Step 9: Convert LTL operators to MLTL (add intervals)
    formula = convert_ltl_to_mltl(formula, interval)
    
    # Step 10: Fix spacing around operators (ensure spaces around |, &, ->, etc.)
    # First, fix broken <-> (if spacing fix broke it) - do this multiple times to catch all cases
    for _ in range(3):
        formula = re.sub(r'<\s*-\s*>', r'<->', formula)
    # Then ensure <-> has spaces around it (but not inside)
    formula = re.sub(r'([^\s-])<->([^\s-])', r'\1 <-> \2', formula)
    # Ensure -> has spaces (but not part of <->) - use negative lookbehind/lookahead
    formula = re.sub(r'(?<!<)->(?!>)', r' -> ', formula)
    formula = re.sub(r'\s+', ' ', formula)  # Clean up multiple spaces
    # Fix | and & operators - add space after if missing (when followed by identifier/paren)
    # Match: ) &a or a&b (no space after &)
    formula = re.sub(r'([^\s])\s*([|&])([a-zA-Z0-9_(!])', r'\1 \2 \3', formula)
    # Also fix cases where there's no space before | or &
    formula = re.sub(r'([a-zA-Z0-9_)])([|&])([^\s])', r'\1 \2 \3', formula)
    
    return formula


def normalize_formula_string(formula: str) -> str:
    """
    Normalize a formula string for comparison.
    Replaces all variable names with 'var' and removes all whitespace.
    """
    # Replace all identifiers (variables) with 'var'
    # Pattern: match identifiers (words starting with letter/underscore, containing letters, digits, dots, underscores)
    # Exclude keywords and operators
    keywords = {'G', 'F', 'H', 'O', 'U', 'R', 'S', 'T', 'true', 'false', 'var', 'bool', 'int', 'INPUT', 'FTSPEC', 'PTSPEC'}
    
    # Find all identifiers and replace with 'var'
    identifier_pattern = r'\b([a-zA-Z_][a-zA-Z0-9_.]*)\b'
    
    def replace_with_var(match):
        ident = match.group(1)
        # Don't replace keywords, numbers, or already normalized 'var'
        if ident in keywords or ident.isdigit() or ident == 'var':
            return ident
        return 'var'
    
    normalized = re.sub(identifier_pattern, replace_with_var, formula)
    
    # Remove all whitespace
    normalized = re.sub(r'\s+', '', normalized)
    
    return normalized


def extract_formula_from_c2po(c2po_content: str) -> str:
    """Extract just the formula part from a C2PO file content."""
    # C2PO format: INPUT ... FTSPEC name: formula;
    # We want to extract just the formula part
    match = re.search(r'FTSPEC\s+\w+:\s*(.+?);', c2po_content, re.DOTALL)
    if match:
        return match.group(1).strip()
    return ""


def extract_formula_from_mltl(mltl_content: str) -> str:
    """Extract the formula from MLTL file (it's just the formula, no headers)."""
    return mltl_content.strip()


def extract_variables_from_formula(formula: str) -> set[str]:
    """Extract all variable names from a formula."""
    variables = set()
    
    # Pattern to match identifiers (variables)
    # Exclude keywords and operators
    keywords = {'G', 'F', 'H', 'O', 'U', 'R', 'S', 'T', 'true', 'false', 'case', 'esac', 'TRUE', 'FALSE'}
    
    # Find all identifiers (including __expr* and other __ prefixed ones)
    pattern = r'\b([a-zA-Z_][a-zA-Z0-9_.]*)\b'
    for match in re.finditer(pattern, formula):
        var = match.group(1)
        if var not in keywords:
            # Include all variables, including __expr* and special props
            variables.add(var)
    
    return variables


def determine_variable_type(var: str, formula: str) -> str:
    """
    Determine if a variable is bool or int based on its usage in the formula.
    
    A variable is int if:
    - It appears in arithmetic operations (+, -, *, /, %)
    - It appears in comparisons with numbers (>, <, >=, <=, ==, !=)
    - It appears in equality with numbers
    
    Otherwise, it's bool.
    """
    # Check for arithmetic operations
    if re.search(rf'\b{re.escape(var)}\s*[+\-*/%]', formula) or \
       re.search(rf'[+\-*/%]\s*\b{re.escape(var)}\b', formula):
        return 'int'
    
    # Check for comparisons with numbers
    if re.search(rf'\b{re.escape(var)}\s*[><=!]+\s*\d+', formula) or \
       re.search(rf'\d+\s*[><=!]+\s*\b{re.escape(var)}\b', formula):
        return 'int'
    
    # Check for equality with numbers
    if re.search(rf'\b{re.escape(var)}\s*=\s*\d+', formula) or \
       re.search(rf'\d+\s*=\s*\b{re.escape(var)}\b', formula):
        return 'int'
    
    # Default to bool
    return 'bool'


def convert_mltl_to_c2po_syntax(formula: str) -> str:
    """
    Convert MLTL formula syntax to C2PO syntax.
    Changes:
    - & -> &&
    - | -> ||
    - = -> == (but not == already)
    - Keep ->, <->, !, G, F, etc.
    - Keep +, >, <, >=, <=, != operators
    """
    # Convert & to && (but not && already)
    formula = re.sub(r'&(?!&)', '&&', formula)
    
    # Convert | to || (but not || already)
    formula = re.sub(r'\|(?!\|)', '||', formula)
    
    # Convert = to == (but not == or != or <= or >= already)
    # Need to be careful: = can be part of ->, <=, >=, !=
    # Pattern: = that's not part of ->, <=, >=, !=, :=, =>
    formula = re.sub(r'(?<![-<:!])=(?![=>])', '==', formula)
    
    return formula


def sanitize_variable_name(name: str) -> str:
    """Sanitize variable name for C2PO (replace dots with underscores)."""
    # Replace dots with underscores
    name = name.replace('.', '_')
    return name


def sanitize_spec_name(name: str) -> str:
    """Sanitize specification name for C2PO (remove invalid characters, limit to 50 chars)."""
    # Replace dots and other invalid chars with underscores
    name = re.sub(r'[.:<>"\'/\\|?*]', '_', name)
    # Replace spaces with underscores
    name = re.sub(r'\s+', '_', name)
    # Remove leading/trailing underscores
    name = name.strip('_')
    # C2PO has a 50 character limit for spec names
    if len(name) > 50:
        name = name[:50]
    return name


def convert_formula_to_c2po(original_formula: str, interval: str = "[0, 1000]", spec_name: str = "spec") -> tuple[str, str]:
    """
    Convert a single LTL formula to C2PO format.
    This version keeps operators like =, +, > instead of converting them to propositions.
    
    Args:
        original_formula: The original LTL formula to convert
        interval: The interval to use for temporal operators
        spec_name: Name for the specification
    
    Returns:
        Tuple of (input_section, ft_spec_section) as strings
    """
    # Extract variables from ORIGINAL formula BEFORE any conversions
    # This preserves type information
    original_vars = extract_variables_from_formula(original_formula)
    
    # Determine variable types from original formula
    bool_vars = []
    int_vars = []
    for var in sorted(original_vars):
        # Skip special expressions that will be handled
        if var.startswith('__expr'):
            # These are intermediate expressions, determine type from usage
            var_type = determine_variable_type(var, original_formula)
            if var_type == 'int':
                int_vars.append(var)
            else:
                bool_vars.append(var)
        else:
            var_type = determine_variable_type(var, original_formula)
            if var_type == 'int':
                int_vars.append(var)
            else:
                bool_vars.append(var)
    
    # Now do the conversions (but DON'T convert operators to propositions)
    formula = original_formula
    
    # Step 1: Convert TRUE/FALSE to true/false
    formula = convert_true_false(formula)
    
    # Step 2: Convert case statements to conjunctions of implications
    formula = convert_case_statements(formula)
    
    # Step 3: For C2PO, we DON'T convert operators or integers
    # Keep =, +, >, <, etc. as operators
    # Keep integer constants as integers (they're valid in C2PO)
    
    # Step 4: Convert LTL operators to MLTL (add intervals)
    formula = convert_ltl_to_mltl(formula, interval)
    
    # Step 5: Fix spacing
    for _ in range(3):
        formula = re.sub(r'<\s*-\s*>', r'<->', formula)
    formula = re.sub(r'([^\s-])<->([^\s-])', r'\1 <-> \2', formula)
    formula = re.sub(r'(?<!<)->(?!>)', r' -> ', formula)
    formula = re.sub(r'\s+', ' ', formula)
    formula = re.sub(r'([^\s])\s*([|&])([a-zA-Z0-9_(!])', r'\1 \2 \3', formula)
    formula = re.sub(r'([a-zA-Z0-9_)])([|&])([^\s])', r'\1 \2 \3', formula)
    
    # Step 6: Convert to C2PO syntax (convert = to ==, & to &&, | to ||)
    formula = convert_mltl_to_c2po_syntax(formula)
    
    # Step 7: Sanitize variable names (replace dots with underscores in formula)
    # We need to replace variable names with dots in the formula
    for var in original_vars:
        if '.' in var:
            sanitized_var = sanitize_variable_name(var)
            # Replace the variable in the formula (be careful with word boundaries)
            formula = re.sub(r'\b' + re.escape(var) + r'\b', sanitized_var, formula)
            # Update the variable lists
            if var in bool_vars:
                bool_vars.remove(var)
                if sanitized_var not in bool_vars:
                    bool_vars.append(sanitized_var)
            if var in int_vars:
                int_vars.remove(var)
                if sanitized_var not in int_vars:
                    int_vars.append(sanitized_var)
    
    # Step 8: Extract special propositions (__intN__) that were created
    special_props = set()
    special_prop_pattern = r'(__int[0-9]+__)'
    for match in re.finditer(special_prop_pattern, formula):
        special_props.add(match.group(1))
    
    # Step 9: Generate INPUT section
    input_lines = ["INPUT"]
    var_decls = []
    
    # Add special propositions as bool (they represent boolean constants)
    if special_props:
        special_bool_vars = sorted(special_props)
        special_line = "    " + ", ".join(special_bool_vars) + ": bool;"
        var_decls.append(special_line)
    
    # Sanitize variable names for declaration
    bool_vars_sanitized = [sanitize_variable_name(var) for var in sorted(bool_vars)]
    int_vars_sanitized = [sanitize_variable_name(var) for var in sorted(int_vars)]
    
    if bool_vars_sanitized:
        # Group bool vars (can declare multiple per line)
        bool_line = "    " + ", ".join(bool_vars_sanitized) + ": bool;"
        var_decls.append(bool_line)
    
    if int_vars_sanitized:
        # Group int vars (can declare multiple per line)
        int_line = "    " + ", ".join(int_vars_sanitized) + ": int;"
        var_decls.append(int_line)
    
    # C2PO requires at least one variable declaration in INPUT section
    # If no variables, add a dummy bool variable
    if not var_decls:
        var_decls.append("    _dummy: bool;")
    
    input_section = "\n".join(input_lines + var_decls)
    
    # Step 10: Generate FTSPEC section with sanitized spec name
    sanitized_spec_name = sanitize_spec_name(spec_name)
    ft_spec_section = f"FTSPEC\n    {sanitized_spec_name}: {formula};"
    
    return input_section, ft_spec_section


def process_xml_file_c2po(xml_path: Path, output_base_dir: Path, seen_formulas: dict[str, set[str]]):
    """Process a single XML file and create C2PO files with multiple interval versions.
    
    Args:
        xml_path: Path to the XML file to process
        output_base_dir: Base directory for output C2PO files
        seen_formulas: Dictionary mapping interval names to sets of normalized formula strings
    """
    print(f"Processing {xml_path}...")
    
    # Define intervals: (interval_string, directory_name)
    intervals = [
        ("[0, 10]", "0_10"),
        ("[0, 100]", "0_100"),
        ("[0, 1000]", "0_1000"),
        ("[10, 100]", "10_100"),
        ("[100, 1000]", "100_1000"),
    ]
    
    # Extract formulas
    formulas = extract_formulas_from_xml(xml_path)
    
    if not formulas:
        print(f"  No formulas found in {xml_path}")
        return
    
    xml_stem = xml_path.stem  # e.g., "properties_1"
    
    print(f"  Found {len(formulas)} formulas")
    
    total_created = 0
    total_skipped = 0
    
    # Process each formula
    for i, formula_data in enumerate(formulas):
        original_formula = formula_data['formula']
        name = formula_data['name']
        index = formula_data['index']
        
        if not original_formula:
            print(f"  Skipping empty formula at index {index}")
            continue
        
        # Skip formulas with 'case' keyword
        if re.search(r'\bcase\b', original_formula, re.IGNORECASE):
            print(f"  Skipping formula {index} ({name}): contains 'case' keyword")
            continue
        
        # Skip formulas with 'next' operator (not supported in C2PO)
        if 'next(' in original_formula or ' next ' in original_formula:
            print(f"  Skipping formula {index} ({name}): contains 'next' operator (not supported in C2PO)")
            continue
        
        # Create filename (ensure .c2po extension)
        # Remove number prefix (index_) from filename
        base_filename = sanitize_filename(name)
        if not base_filename.endswith('.c2po'):
            filename = base_filename + '.c2po'
        else:
            filename = base_filename
        
        # Process each interval version
        for interval_str, interval_dir in intervals:
            try:
                # Convert to C2PO with this interval
                input_section, ft_spec_section = convert_formula_to_c2po(
                    original_formula, interval_str, name
                )
                
                # Combine into full C2PO file
                c2po_content = f"{input_section}\n\n{ft_spec_section}\n"
                
                # Extract just the formula part and normalize for comparison
                formula_part = extract_formula_from_c2po(c2po_content)
                normalized_formula = normalize_formula_string(formula_part)
                
                # Initialize seen_formulas for this interval if needed
                if interval_dir not in seen_formulas:
                    seen_formulas[interval_dir] = set()
                
                # Check if we've seen this formula before (for this interval)
                if normalized_formula in seen_formulas[interval_dir]:
                    total_skipped += 1
                    continue
                
                # Mark as seen
                seen_formulas[interval_dir].add(normalized_formula)
                
                # Create output directory for this interval
                output_dir = output_base_dir / interval_dir / xml_stem
                output_dir.mkdir(parents=True, exist_ok=True)
                output_path = output_dir / filename
                
                # Write C2PO file
                with open(output_path, 'w') as f:
                    f.write(c2po_content)
                
                total_created += 1
                
            except Exception as e:
                print(f"  Error processing formula {index} ({name}) with interval {interval_str}: {e}")
                continue
    
    print(f"  Created {total_created} files, skipped {total_skipped} duplicates")


def process_xml_file(xml_path: Path, output_base_dir: Path, seen_formulas: dict[str, set[str]]):
    """Process a single XML file and create MLTL files with multiple interval versions.
    
    Args:
        xml_path: Path to the XML file to process
        output_base_dir: Base directory for output MLTL files
        seen_formulas: Dictionary mapping interval names to sets of normalized MLTL formula strings
    """
    print(f"Processing {xml_path}...")
    
    # Define intervals: (interval_string, directory_name)
    intervals = [
        ("[0, 10]", "0_10"),
        ("[0, 100]", "0_100"),
        ("[0, 1000]", "0_1000"),
        ("[10, 100]", "10_100"),
        ("[100, 1000]", "100_1000"),
    ]
    
    # Extract formulas
    formulas = extract_formulas_from_xml(xml_path)
    
    if not formulas:
        print(f"  No formulas found in {xml_path}")
        return
    
    xml_stem = xml_path.stem  # e.g., "properties_1"
    
    print(f"  Found {len(formulas)} formulas")
    
    total_created = 0
    total_skipped = 0
    
    # Process each formula
    for i, formula_data in enumerate(formulas):
        original_formula = formula_data['formula']
        name = formula_data['name']
        index = formula_data['index']
        
        if not original_formula:
            print(f"  Skipping empty formula at index {index}")
            continue
        
        # Skip formulas with 'case' keyword
        if re.search(r'\bcase\b', original_formula, re.IGNORECASE):
            print(f"  Skipping formula {index} ({name}): contains 'case' keyword")
            continue
        
        # Create filename (ensure .mltl extension)
        # Remove number prefix (index_) from filename
        base_filename = sanitize_filename(name)
        if not base_filename.endswith('.mltl'):
            filename = base_filename + '.mltl'
        else:
            filename = base_filename
        
        # Process each interval version
        for interval_str, interval_dir in intervals:
            try:
                # Convert to MLTL with this interval
                mltl_formula = convert_formula_to_mltl(original_formula, interval_str)
                
                # Normalize for comparison: extract formula and normalize (replace vars with 'var', remove whitespace)
                formula_part = extract_formula_from_mltl(mltl_formula)
                normalized_formula = normalize_formula_string(formula_part)
                
                # Initialize seen_formulas for this interval if needed
                if interval_dir not in seen_formulas:
                    seen_formulas[interval_dir] = set()
                
                # Check if we've seen this formula before (for this interval)
                if normalized_formula in seen_formulas[interval_dir]:
                    total_skipped += 1
                    continue
                
                # Mark as seen
                seen_formulas[interval_dir].add(normalized_formula)
                
                # Create output directory for this interval
                output_dir = output_base_dir / interval_dir / xml_stem
                output_dir.mkdir(parents=True, exist_ok=True)
                output_path = output_dir / filename
                
                # Write MLTL file
                with open(output_path, 'w') as f:
                    f.write(mltl_formula + '\n')
                
                total_created += 1
                
            except Exception as e:
                print(f"  Error processing formula {index} ({name}) with interval {interval_str}: {e}")
                continue
    
    print(f"  Created {total_created} files, skipped {total_skipped} duplicates")


def main():
    """Main function to process all XML files."""
    # Base directory for XML files
    xml_dir = Path(__file__).parent / "properties"
    
    # Output base directory
    c2po_output_dir = Path(__file__).parent / "c2po"
    
    # Find all properties_X.xml files
    xml_files = sorted(xml_dir.glob("properties_*.xml"))
    
    if not xml_files:
        print(f"No XML files found in {xml_dir}")
        return
    
    print(f"Found {len(xml_files)} XML files")
    print(f"C2PO output directory: {c2po_output_dir}\n")
    
    # Track seen formulas per interval to avoid duplicates
    # Dictionary mapping interval directory name to set of normalized formulas
    seen_formulas_c2po: dict[str, set[str]] = {}
    
    # Process each XML file for C2PO
    print("=" * 60)
    print("Converting to C2PO format...")
    print("=" * 60)
    for xml_file in xml_files:
        process_xml_file_c2po(xml_file, c2po_output_dir, seen_formulas_c2po)
        print()
    
    # Print summary
    total_unique_c2po = sum(len(formulas) for formulas in seen_formulas_c2po.values())
    
    print("=" * 60)
    print("Conversion complete!")
    print("=" * 60)
    print("\nC2PO conversion:")
    for interval_dir, formulas in sorted(seen_formulas_c2po.items()):
        print(f"  {interval_dir}: {len(formulas)} unique formulas")
    print(f"  Total unique formulas (across all intervals): {total_unique_c2po}")


if __name__ == "__main__":
    main()

