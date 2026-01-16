#!/usr/bin/env python3
"""
Script to generate .equiv files from mltl_rewrites.json.
Each rule in the JSON array gets a corresponding .equiv file named by its index.

Generated on 2025-10-22 by Cursor AI.
"""

import argparse
import json
from pathlib import Path


def generate_equiv_file(rule, index, output_dir):
    """
    Generate a .equiv file for a single rule.
    
    Args:
        rule: Dictionary containing 'pre', 'post', 'constraints', and 'birewrite'
        index: Zero-based index of the rule in the JSON array
        output_dir: Directory where the .equiv file should be written
    """
    # Create filename with zero-padded 3-digit index (e.g., rule_000.equiv)
    filename = f"rule_{index:03d}.equiv"
    filepath = output_dir / filename
    lines = []
    
    if rule.get('constraints'):
        for constraint in rule['constraints']:
            lines.append(f"c: {constraint}")
    
    lines.append(rule['pre'])
    lines.append(rule['post'])
    lines.append("")
    
    content = "\n".join(lines)
    filepath.write_text(content)
    
    print(f"Generated {filepath}")


def main():
    parser = argparse.ArgumentParser(
        description="Generate .equiv files from a JSON file containing MLTL rewrite rules."
    )
    parser.add_argument(
        "json_file",
        type=str,
        help="Path to the JSON file containing rewrite rules"
    )
    parser.add_argument(
        "output_dir",
        type=str,
        help="Path to the output directory where .equiv files will be written"
    )
    
    args = parser.parse_args()
    
    # Convert to Path objects
    json_path = Path(args.json_file)
    output_dir = Path(args.output_dir)
    
    # Validate JSON file exists
    if not json_path.exists():
        print(f"Error: JSON file not found: {json_path}")
        return 1
    
    # Create output directory if it doesn't exist
    output_dir.mkdir(parents=True, exist_ok=True)
    
    # Read the JSON file
    try:
        with open(json_path, 'r') as f:
            rules = json.load(f)
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON file: {e}")
        return 1
    
    # Validate that rules is a list
    if not isinstance(rules, list):
        print("Error: JSON file must contain an array of rules")
        return 1
    
    # Generate .equiv file for each rule
    for index, rule in enumerate(rules):
        generate_equiv_file(rule, index, output_dir)
    
    print(f"\nGenerated {len(rules)} .equiv files in {output_dir}")
    return 0


if __name__ == "__main__":
    exit(main())

