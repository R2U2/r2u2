#!/usr/bin/env python3
"""
Script to generate .egg files from .equiv files.

This script:
1. Parses .equiv files using the parser from compiler/c2po/parse_equiv.py
2. Converts the parsed formulas to egglog format
3. Converts constraints to :when format
4. Checks rewrites.json to determine if a rule is a birewrite
5. Generates corresponding .egg files

Generated on 2025-12-22 by Cursor AI.
"""
import argparse
import json
import sys
from pathlib import Path
from typing import Optional, cast, Union

# Add the compiler directory to the path so we can import c2po modules
script_dir = Path(__file__).parent
compiler_dir = script_dir.parent.parent
sys.path.insert(0, str(compiler_dir))

# Import after path setup
from c2po import cpt  # noqa: E402
from c2po.parse_equiv import parse_equiv  # noqa: E402


def expr_to_egglog(expr: cpt.Expression, context: Optional[cpt.Context] = None) -> str:
    """
    Convert an MLTL expression to egglog format (without let bindings).
    This is similar to to_egglog but returns just the expression directly.
    """
    if isinstance(expr, cpt.Constant):
        if isinstance(expr.value, bool):
            return f"(Bool {str(expr.value).lower()})"
        else:
            return str(expr.value)
    elif isinstance(expr, cpt.Signal):
        return expr.symbol
    elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
        return f"(Not {expr_to_egglog(expr.children[0], context)})"
    elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_IMPLIES):
        return f"(Implies {expr_to_egglog(expr.children[0], context)} {expr_to_egglog(expr.children[1], context)})"
    elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_EQUIV):
        return f"(Equiv {expr_to_egglog(expr.children[0], context)} {expr_to_egglog(expr.children[1], context)})"
    elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
        arity = len(expr.children)
        children_str = " ".join(expr_to_egglog(c, context) for c in expr.children)
        return f"(And{arity} {children_str})"
    elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
        arity = len(expr.children)
        children_str = " ".join(expr_to_egglog(c, context) for c in expr.children)
        return f"(Or{arity} {children_str})"
    elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
        expr = cast(cpt.TemporalOperator, expr)
        interval_str = interval_to_egglog(expr.interval)
        return f"(Global {interval_str} {expr_to_egglog(expr.children[0], context)})"
    elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
        expr = cast(cpt.TemporalOperator, expr)
        interval_str = interval_to_egglog(expr.interval)
        return f"(Future {interval_str} {expr_to_egglog(expr.children[0], context)})"
    elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
        expr = cast(cpt.TemporalOperator, expr)
        interval_str = interval_to_egglog(expr.interval)
        return f"(Until {interval_str} {expr_to_egglog(expr.children[0], context)} {expr_to_egglog(expr.children[1], context)})"
    elif cpt.is_operator(expr, cpt.OperatorKind.RELEASE):
        expr = cast(cpt.TemporalOperator, expr)
        interval_str = interval_to_egglog(expr.interval)
        return f"(Release {interval_str} {expr_to_egglog(expr.children[0], context)} {expr_to_egglog(expr.children[1], context)})"
    else:
        raise ValueError(f"Unsupported expression type: {type(expr)}")


def interval_to_egglog(interval: Union[cpt.SymbolicInterval, cpt.ConcreteInterval]) -> str:
    """Convert a SymbolicInterval or ConcreteInterval to egglog format."""
    if isinstance(interval, cpt.ConcreteInterval):
        # ConcreteInterval has int lb and ub
        return f"(Interval {interval.lb} {interval.ub})"
    else:
        # SymbolicInterval has Expression lb and ub
        lb_str = constraint_expr_to_egglog(interval.lb)
        ub_str = constraint_expr_to_egglog(interval.ub)
        return f"(Interval {lb_str} {ub_str})"


def constraint_expr_to_egglog(expr: cpt.Expression) -> str:
    """
    Convert a constraint expression to egglog format for use in intervals and :when clauses.
    This converts arithmetic and comparison operations to SMT-like format.
    """
    if isinstance(expr, cpt.SymbolicIntervalVariable):
        return expr.symbol
    elif isinstance(expr, cpt.MissionTime):
        return "M"
    elif isinstance(expr, cpt.Constant):
        return str(expr.value)
    elif cpt.is_operator(expr, cpt.OperatorKind.EQUAL):
        return f"(= {constraint_expr_to_egglog(expr.children[0])} {constraint_expr_to_egglog(expr.children[1])})"
    elif cpt.is_operator(expr, cpt.OperatorKind.NOT_EQUAL):
        return f"(not (= {constraint_expr_to_egglog(expr.children[0])} {constraint_expr_to_egglog(expr.children[1])}))"
    elif cpt.is_operator(expr, cpt.OperatorKind.GREATER_THAN):
        return f"(> {constraint_expr_to_egglog(expr.children[0])} {constraint_expr_to_egglog(expr.children[1])})"
    elif cpt.is_operator(expr, cpt.OperatorKind.GREATER_THAN_OR_EQUAL):
        return f"(>= {constraint_expr_to_egglog(expr.children[0])} {constraint_expr_to_egglog(expr.children[1])})"
    elif cpt.is_operator(expr, cpt.OperatorKind.LESS_THAN):
        return f"(< {constraint_expr_to_egglog(expr.children[0])} {constraint_expr_to_egglog(expr.children[1])})"
    elif cpt.is_operator(expr, cpt.OperatorKind.LESS_THAN_OR_EQUAL):
        return f"(<= {constraint_expr_to_egglog(expr.children[0])} {constraint_expr_to_egglog(expr.children[1])})"
    elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_ADD):
        return f"(+ {constraint_expr_to_egglog(expr.children[0])} {constraint_expr_to_egglog(expr.children[1])})"
    elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_SUBTRACT):
        return f"(- {constraint_expr_to_egglog(expr.children[0])} {constraint_expr_to_egglog(expr.children[1])})"
    elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_MULTIPLY):
        return f"(* {constraint_expr_to_egglog(expr.children[0])} {constraint_expr_to_egglog(expr.children[1])})"
    elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_DIVIDE):
        return f"(/ {constraint_expr_to_egglog(expr.children[0])} {constraint_expr_to_egglog(expr.children[1])})"
    elif cpt.is_operator(expr, cpt.OperatorKind.MIN):
        # min(a, b) in egglog/SMT format
        return f"(min {constraint_expr_to_egglog(expr.children[0])} {constraint_expr_to_egglog(expr.children[1])})"
    elif cpt.is_operator(expr, cpt.OperatorKind.MAX):
        # max(a, b) in egglog/SMT format
        return f"(max {constraint_expr_to_egglog(expr.children[0])} {constraint_expr_to_egglog(expr.children[1])})"
    else:
        raise ValueError(f"Unsupported constraint expression type: {type(expr)}")


def constraints_to_when(constraints: list[cpt.Expression]) -> str:
    """
    Convert a list of constraint expressions to a :when clause format.
    Returns the string to be used in the :when attribute.
    """
    if not constraints:
        return ""
    
    constraint_strs = [constraint_expr_to_egglog(c) for c in constraints]
    return f":when ({' '.join(constraint_strs)})"


def main():
    # Parse command-line arguments
    parser = argparse.ArgumentParser(
        description="Generate .egg files from .equiv files",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s equiv/ rewrites.json output.egg
  %(prog)s /path/to/equiv/ /path/to/rewrites.json /path/to/output.egg
        """
    )
    parser.add_argument(
        "equiv_dir",
        type=Path,
        help="Directory containing *.equiv files"
    )
    parser.add_argument(
        "json_file",
        type=Path,
        help="JSON file with rewrite rules (rewrites.json)"
    )
    parser.add_argument(
        "output_directory",
        type=Path,
        help="Output directory to write the .egg files to"
    )
    
    args = parser.parse_args()
    
    # Get paths from arguments
    equiv_dir = args.equiv_dir
    rewrites_json = args.json_file
    output_directory = args.output_directory
    
    # Check if paths exist
    if not equiv_dir.exists() or not equiv_dir.is_dir():
        print(f"Error: Input directory not found: {equiv_dir}", file=sys.stderr)
        sys.exit(1)
    
    if not rewrites_json.exists() or not rewrites_json.is_file():
        print(f"Error: JSON file not found: {rewrites_json}", file=sys.stderr)
        sys.exit(1)
    
    # Create output directory if it doesn't exist
    output_directory.mkdir(parents=True, exist_ok=True)
    
    # Load rewrites.json to get birewrite information
    with open(rewrites_json, 'r') as f:
        rewrites = json.load(f)
    
    # Get all .equiv files
    equiv_files = sorted(equiv_dir.glob("*.equiv"))
    
    print(f"Found {len(equiv_files)} .equiv files")
    print(f"Output directory: {output_directory}")
    print()
    
    success_count = 0
    error_count = 0
    temporal_rules_content = []
    const_folding_rules_content = []
    
    # Process each .equiv file
    for equiv_file in equiv_files:
        # Extract rule number from filename (e.g., "rule_000.equiv" -> 0)
        rule_num_str = equiv_file.stem.replace("rule_", "")
        try:
            rule_index = int(rule_num_str)
        except ValueError:
            print(f"Warning: Could not parse rule number from {equiv_file.name}, skipping", file=sys.stderr)
            error_count += 1
            continue
        
        if rule_index >= len(rewrites):
            print(f"Warning: Rule index {rule_index} out of range in {equiv_file.name}, skipping", file=sys.stderr)
            error_count += 1
            continue
        
        print(f"Processing {equiv_file.name}...", end=" ", flush=True)
        
        try:
            # Parse the .equiv file
            context = cpt.Context()
            result = parse_equiv(context, {"filename": str(equiv_file)})
            if result is None:
                print("✗ Parse error")
                error_count += 1
                continue
            
            program = result
            constraints = context.constraints
            
            # Get the pre and post formulas
            specs = program.get_specs()
            if len(specs) != 2:
                print(f"✗ Expected 2 formulas (pre and post), got {len(specs)}")
                error_count += 1
                continue
            
            pre_spec = specs[0]
            post_spec = specs[1]
            
            # Check if they are Formulas (not Contracts)
            if not isinstance(pre_spec, cpt.Formula) or not isinstance(post_spec, cpt.Formula):
                print(f"✗ Expected Formula types, got {type(pre_spec)} and {type(post_spec)}")
                error_count += 1
                continue
            
            # Convert to egglog format
            pre_expr = expr_to_egglog(pre_spec.get_expr())
            post_expr = expr_to_egglog(post_spec.get_expr())

            is_subsumed = False
            for expr in cpt.postorder(pre_spec.get_expr(), context):
                if repr(expr) == repr(post_spec.get_expr()):
                    is_subsumed = True
                    break
            
            # Get birewrite information from rewrites.json
            is_birewrite = rewrites[rule_index].get("birewrite", False)
            
            # Convert constraints to :when format
            when_clause = constraints_to_when(constraints)
            
            # Generate the rule content
            rule_type = "birewrite" if is_birewrite else "rewrite"
            
            rule_content = f"({rule_type}\n"
            rule_content += f"  {pre_expr}\n"
            rule_content += f"  {post_expr}\n"
            if when_clause:
                rule_content += f"  {when_clause}\n"

            if is_subsumed:
                rule_content += "  :subsume\n"

            # If the post expression is a constant, use the const-folding ruleset
            # If we do not, the performance of egglog is terrible
            if "Bool" in post_expr:
                rule_content += "  :ruleset const-folding\n"
                rule_content += ")\n"
                const_folding_rules_content.append(rule_content)
            else:
                rule_content += "  :ruleset mltl-rewrites\n"
                rule_content += ")\n"
                temporal_rules_content.append(rule_content)
            
            print("✓")
            success_count += 1
            
        except Exception as e:
            print(f"✗ Error: {e}")
            import traceback
            traceback.print_exc()
            error_count += 1
    
    # Write all rules to a single file
    print()
    print(f"Writing {len(temporal_rules_content)} temporal rules to {output_directory / 'temporal.egg'}...", end=" ", flush=True)
    
    try:
        with open(output_directory / "temporal.egg", 'w') as f:
            # Write all rules
            for rule_content in temporal_rules_content:
                f.write(rule_content)
                f.write("\n")
        
        print("✓")
    except Exception as e:
        print(f"✗ Error writing output file: {e}")
        error_count += 1

    print(f"Writing {len(const_folding_rules_content)} const-folding rules to {output_directory / 'const_folding.egg'}...", end=" ", flush=True)
    try:
        with open(output_directory / "const_folding.egg", 'w') as f:
            # Write all rules
            for rule_content in const_folding_rules_content:
                f.write(rule_content)
                f.write("\n")
        
        print("✓")
    except Exception as e:
        print(f"✗ Error writing output file: {e}")
        error_count += 1
    print()
    print(f"Summary: {success_count} rules processed, {error_count} failed")
    print(f"Output written to: {output_directory}")


if __name__ == "__main__":
    main()

