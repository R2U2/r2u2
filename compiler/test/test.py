from itertools import count
from typing import List, Tuple

from numpy import equal
from c2po.main import compile, ReturnCode
from c2po.ast import *

TEST_DIR = "./"
TYPE_CHECK_DIR = f"{TEST_DIR}typecheck/"
CSE_DIR = f"{TEST_DIR}cse/"
OPERATORS_DIR = f"{TEST_DIR}operators/"
SET_AGG_DIR = f"{TEST_DIR}set_agg/"
AT_DIR = f"{TEST_DIR}atomic_checker/"

class TestCSE():

    def test_cse_basic_bz(self):
        csv_filename = f"{CSE_DIR}cse.csv"
        mltl_filename = f"{CSE_DIR}basic.mltl"

        (status, ft_asm, pt_asm, bz_asm, at_asm, scq_asm) = compile(mltl_filename, csv_filename, enable_bz=True)
        assert status == ReturnCode.SUCCESS.value

        assert len(bz_asm) == 4
        assert len(ft_asm) == 9
        assert len(scq_asm) == len(ft_asm)-1
        assert len(pt_asm) == 1

        (status, ft_asm, pt_asm, bz_asm, at_asm, scq_asm) = compile(mltl_filename, csv_filename, enable_bz=True, enable_cse=True)
        assert status == ReturnCode.SUCCESS.value

        assert len(bz_asm) == 2
        assert len(ft_asm) == 6
        assert len(scq_asm) == len(ft_asm)-1
        assert len(pt_asm) == 1

    def test_cse_basic_at(self):
        csv_filename = f"{CSE_DIR}cse.csv"
        mltl_filename = f"{CSE_DIR}at.mltl"

        (status, ft_asm, pt_asm, bz_asm, at_asm, scq_asm) = compile(mltl_filename, csv_filename, enable_at=True)
        assert status == ReturnCode.SUCCESS.value

        assert len(at_asm) == 2
        assert len(ft_asm) == 9
        assert len(scq_asm) == len(ft_asm)-1
        assert len(pt_asm) == 1

        (status, ft_asm, pt_asm, bz_asm, at_asm, scq_asm) = compile(mltl_filename, csv_filename, enable_at=True, enable_cse=True)
        assert status == ReturnCode.SUCCESS.value

        assert len(at_asm) == 2
        assert len(ft_asm) == 6
        assert len(scq_asm) == len(ft_asm)-1
        assert len(pt_asm) == 1


class TestOperators():

    def test_logic(self):
        csv_filename = f"{OPERATORS_DIR}operators.csv"
        mltl_filename = f"{OPERATORS_DIR}logic.mltl"

        (status, ft_asm, pt_asm, bz_asm, at_asm, scq_asm) = compile(mltl_filename, csv_filename, enable_bz=True, enable_cse=True, enable_extops=True, enable_assemble=False)
        assert status == ReturnCode.SUCCESS.value

        assert isinstance(bz_asm[0], Signal)
        assert isinstance(bz_asm[1], Signal)

        b0 = bz_asm[0] if bz_asm[0].name == "b0" else bz_asm[1]
        b1 = bz_asm[1] if bz_asm[1].name == "b1" else bz_asm[0]

        ops_tested: List[type] = []
        for instr in ft_asm:
            ops_tested.append(type(instr))
            if isinstance(instr, LogicalNegate):
                assert b0 in instr.get_children()
            elif isinstance(instr, LogicalAnd) or isinstance(instr, LogicalOr) or isinstance(instr, LogicalIff):
                assert len(instr.get_children()) == 2
                assert b0 in instr.get_children()
                assert b1 in instr.get_children()
            elif isinstance(instr, LogicalImplies):
                assert len(instr.get_children()) == 2
                assert b0 == instr.get_child(0)
                assert b1 == instr.get_child(1)

        assert LogicalNegate in ops_tested
        assert LogicalAnd in ops_tested
        assert LogicalOr in ops_tested
        assert LogicalIff in ops_tested
        assert LogicalImplies in ops_tested

        assert len(ft_asm) == 13

    def test_temporal(self):
        csv_filename = f"{OPERATORS_DIR}operators.csv"
        mltl_filename = f"{OPERATORS_DIR}temporal.mltl"

        (status, ft_asm, pt_asm, bz_asm, at_asm, scq_asm) = compile(mltl_filename, csv_filename, enable_bz=True, enable_cse=True, enable_extops=True, enable_assemble=False)
        assert status == ReturnCode.SUCCESS.value

        assert isinstance(bz_asm[0], Signal)
        assert isinstance(bz_asm[1], Signal)

        b0 = bz_asm[0] if bz_asm[0].name == "b0" else bz_asm[1]
        b1 = bz_asm[1] if bz_asm[1].name == "b1" else bz_asm[0]

        ops_tested: List[type] = []
        for instr in ft_asm:
            ops_tested.append(type(instr))
            if isinstance(instr, Global) or isinstance(instr, Future):
                assert b0 in instr.get_children()
            elif isinstance(instr, Until) or isinstance(instr, Release):
                assert len(instr.get_children()) == 2
                assert b0 == instr.get_child(0)
                assert b1 == instr.get_child(1)

        assert Global in ops_tested
        assert Future in ops_tested
        assert Until in ops_tested
        assert Release in ops_tested

        assert len(ft_asm) == 11

        ops_tested = []
        for instr in pt_asm:
            ops_tested.append(type(instr))
            if isinstance(instr, Historical) or isinstance(instr, Once):
                assert b0 in instr.get_children()
            elif isinstance(instr, Since):
                assert len(instr.get_children()) == 2
                assert b0 == instr.get_child(0)
                assert b1 == instr.get_child(1)

        assert Historical in ops_tested
        assert Once in ops_tested
        assert Since in ops_tested

        assert len(pt_asm) == 9

    def test_relational(self):
        csv_filename = f"{OPERATORS_DIR}operators.csv"
        mltl_filename = f"{OPERATORS_DIR}relational.mltl"

        (status, ft_asm, pt_asm, bz_asm, at_asm, scq_asm) = compile(mltl_filename, csv_filename, enable_bz=True, enable_cse=True, enable_extops=True, enable_assemble=False)
        assert status == ReturnCode.SUCCESS.value
        
        i0,i1,f0,f1 = None, None, None, None
        for instr in bz_asm:
            if instr.name == "i0":
                i0 = instr
            elif instr.name == "i1":
                i1 = instr
            elif instr.name == "f0":
                f0 = instr
            elif instr.name == "f1":
                f1 = instr
        assert i0 and i1 and f0 and f1

        ops_tested: List[Tuple[type,type]] = []
        for instr in bz_asm:
            if len(instr.get_children()) > 0:
                ops_tested.append((type(instr.get_child(0).type),type(instr)))
            if (isinstance(instr, Equal) or isinstance(instr, NotEqual)) and instr.get_child(0).type == INT(False):
                assert len(instr.get_children()) == 2
                assert i0 == instr.get_child(0)
                assert i1 == instr.get_child(1)
            elif (isinstance(instr, GreaterThan) or isinstance(instr, LessThan) or isinstance(instr, GreaterThanOrEqual) or isinstance(instr, LessThanOrEqual)) and instr.get_child(0).type == INT(False):
                assert len(instr.get_children()) == 2
                assert i0 in instr.get_children()
                assert i1 in instr.get_children()
            elif (isinstance(instr, Equal) or isinstance(instr, NotEqual)) and instr.get_child(0).type == FLOAT(False):
                assert len(instr.get_children()) == 2
                assert f0 == instr.get_child(0)
                assert f1 == instr.get_child(1)
            elif (isinstance(instr, GreaterThan) or isinstance(instr, LessThan) or isinstance(instr, GreaterThanOrEqual) or isinstance(instr, LessThanOrEqual)) and instr.get_child(0).type == FLOAT(False):
                assert len(instr.get_children()) == 2
                assert f0 in instr.get_children()
                assert f1 in instr.get_children()

        assert (INT,Equal) in ops_tested
        assert (INT,NotEqual) in ops_tested
        assert (INT,GreaterThan) in ops_tested
        assert (INT,LessThan) in ops_tested
        assert (INT,GreaterThanOrEqual) in ops_tested
        assert (INT,LessThanOrEqual) in ops_tested
        assert (FLOAT,Equal) in ops_tested
        assert (FLOAT,NotEqual) in ops_tested
        assert (FLOAT,GreaterThan) in ops_tested
        assert (FLOAT,LessThan) in ops_tested

        assert len(bz_asm) == 14

    def test_arithmetic(self):
        csv_filename = f"{OPERATORS_DIR}operators.csv"
        mltl_filename = f"{OPERATORS_DIR}arithmetic.mltl"

        (status, ft_asm, pt_asm, bz_asm, at_asm, scq_asm) = compile(mltl_filename, csv_filename, enable_bz=True, enable_cse=True, enable_extops=True, enable_assemble=False)
        assert status == ReturnCode.SUCCESS.value
        
        i0,i1,f0,f1 = None, None, None, None
        for instr in bz_asm:
            if instr.name == "i0":
                i0 = instr
            elif instr.name == "i1":
                i1 = instr
            elif instr.name == "f0":
                f0 = instr
            elif instr.name == "f1":
                f1 = instr
        assert i0 and i1 and f0 and f1

        ops_tested: List[Tuple[type,type]] = []
        for instr in bz_asm:
            ops_tested.append((type(instr.type),type(instr)))
            if isinstance(instr, ArithmeticNegate) and instr.get_child(0).type == INT(False):
                assert len(instr.get_children()) == 1
                assert i0 == instr.get_child(0)
            elif (isinstance(instr, ArithmeticAdd) or isinstance(instr, ArithmeticSubtract) or isinstance(instr, ArithmeticMultiply) or isinstance(instr, ArithmeticDivide) or isinstance(instr, ArithmeticModulo)) and instr.get_child(0).type == INT(False):
                assert len(instr.get_children()) == 2
                assert i0 == instr.get_child(0)
                assert i1 == instr.get_child(1)
            elif isinstance(instr, ArithmeticNegate) and instr.get_child(0).type == FLOAT(False):
                assert len(instr.get_children()) == 1
                assert f0 == instr.get_child(0)
            elif (isinstance(instr, ArithmeticAdd) or isinstance(instr, ArithmeticSubtract) or isinstance(instr, ArithmeticMultiply) or isinstance(instr, ArithmeticDivide) or isinstance(instr, ArithmeticModulo)) and instr.get_child(0).type == FLOAT(False):
                assert len(instr.get_children()) == 2
                assert f0 == instr.get_child(0)
                assert f1 == instr.get_child(1)
                
        assert (INT,ArithmeticNegate) in ops_tested
        assert (INT,ArithmeticAdd) in ops_tested
        assert (INT,ArithmeticSubtract) in ops_tested
        assert (INT,ArithmeticMultiply) in ops_tested
        assert (INT,ArithmeticDivide) in ops_tested
        assert (INT,ArithmeticModulo) in ops_tested
        assert (FLOAT,ArithmeticNegate) in ops_tested
        assert (FLOAT,ArithmeticAdd) in ops_tested
        assert (FLOAT,ArithmeticSubtract) in ops_tested
        assert (FLOAT,ArithmeticMultiply) in ops_tested
        assert (FLOAT,ArithmeticDivide) in ops_tested

        assert len(bz_asm) == 28

    def test_bitwise(self):
        csv_filename = f"{OPERATORS_DIR}operators.csv"
        mltl_filename = f"{OPERATORS_DIR}bitwise.mltl"

        (status, ft_asm, pt_asm, bz_asm, at_asm, scq_asm) = compile(mltl_filename, csv_filename, enable_bz=True, enable_cse=True, enable_extops=True, enable_assemble=False)
        assert status == ReturnCode.SUCCESS.value
        
        i0,i1 = None, None
        for instr in bz_asm:
            if instr.name == "i0":
                i0 = instr
            elif instr.name == "i1":
                i1 = instr
        assert i0 and i1

        ops_tested: List[type] = []
        for instr in bz_asm:
            ops_tested.append(type(instr))
            if isinstance(instr, BitwiseNegate):
                assert i0 in instr.get_children()
            elif isinstance(instr, BitwiseAnd) or isinstance(instr, BitwiseOr) or isinstance(instr, BitwiseXor):
                assert len(instr.get_children()) == 2
                assert i0 in instr.get_children()
                assert i1 in instr.get_children()
            elif isinstance(instr, BitwiseShiftLeft) or isinstance(instr, BitwiseShiftRight):
                assert len(instr.get_children()) == 2
                assert i0 == instr.get_child(0)
                assert i1 == instr.get_child(1)

        assert BitwiseNegate in ops_tested
        assert BitwiseAnd in ops_tested
        assert BitwiseOr in ops_tested
        assert BitwiseXor in ops_tested
        assert BitwiseShiftLeft in ops_tested
        assert BitwiseShiftRight in ops_tested

        assert len(bz_asm) == 15


class TestSetAgg():

    def test_basic(self):
        csv_filename = f"{SET_AGG_DIR}set_agg.csv"
        mltl_filename = f"{SET_AGG_DIR}basic.mltl"

        (status, ft_asm, pt_asm, bz_asm, at_asm, scq_asm) = compile(mltl_filename, csv_filename, enable_bz=True, enable_cse=True, enable_extops=True, enable_assemble=False)
        assert status == ReturnCode.SUCCESS.value

        assert len(bz_asm) == 9
        
        b0,b1,b2,i = None, None, None, None
        for instr in bz_asm:
            if instr.name == "b0":
                b0 = instr
            elif instr.name == "b1":
                b1 = instr
            elif instr.name == "b2":
                b2 = instr
            elif instr.name == "1":
                i = instr
        assert b0 and b1 and b2 and i

        ops_tested: List[type] = []
        for instr in bz_asm:
            ops_tested.append(type(instr))
            if isinstance(instr, Count):
                assert len(instr.get_children()) == 3
                assert b0 in instr.get_children() 
                assert b1 in instr.get_children()
                assert b2 in instr.get_children()
            elif isinstance(instr, Equal):
                assert len(instr.get_children()) == 2
                assert i in instr.get_children() 
            elif isinstance(instr, GreaterThanOrEqual):
                assert len(instr.get_children()) == 2
                assert i in instr.get_children() 
            elif isinstance(instr, LessThanOrEqual):
                assert len(instr.get_children()) == 2
                assert i in instr.get_children() 

        assert ArithmeticAdd in ops_tested
        assert Integer in ops_tested
        assert Equal in ops_tested
        assert GreaterThanOrEqual in ops_tested
        assert LessThanOrEqual in ops_tested

        assert len(ft_asm) == 15

    def test_var_set(self):
        csv_filename = f"{SET_AGG_DIR}set_agg.csv"
        mltl_filename = f"{SET_AGG_DIR}var_set.mltl"

        (status, ft_asm, pt_asm, bz_asm, at_asm, scq_asm) = compile(mltl_filename, csv_filename, enable_bz=True, enable_cse=True, enable_extops=True, enable_assemble=False)
        assert status == ReturnCode.SUCCESS.value

    def test_struct_set(self):
        csv_filename = f"{SET_AGG_DIR}set_agg.csv"
        mltl_filename = f"{SET_AGG_DIR}struct_set.mltl"

        (status, ft_asm, pt_asm, bz_asm, at_asm, scq_asm) = compile(mltl_filename, csv_filename, enable_bz=True, enable_cse=True, enable_extops=True, enable_assemble=False)
        assert status == ReturnCode.SUCCESS.value

    def test_struct_set_combo(self):
        csv_filename = f"{SET_AGG_DIR}set_agg.csv"
        mltl_filename = f"{SET_AGG_DIR}struct_set_combo.mltl"

        (status, ft_asm, pt_asm, bz_asm, at_asm, scq_asm) = compile(mltl_filename, csv_filename, enable_bz=True, enable_cse=True, enable_extops=True, enable_assemble=False)
        assert status == ReturnCode.SUCCESS.value


class TestAtomicCheckers():

    def test_bool(self):
        csv_filename = f"{AT_DIR}atomic_checker.csv"
        mltl_filename = f"{AT_DIR}bool.mltl"

        (status, ft_asm, pt_asm, bz_asm, at_asm, scq_asm) = compile(mltl_filename, csv_filename, enable_at=True, enable_cse=True, enable_extops=True, enable_assemble=False)
        assert status == ReturnCode.SUCCESS.value

        assert len(at_asm) == 1

        instr = at_asm[0]
        assert instr.args[0].name == "b"
        assert instr.filter == "bool"
        assert instr.rel_op.symbol == "=="
        assert instr.compare.name == "True"

    def test_int(self):
        csv_filename = f"{AT_DIR}atomic_checker.csv"
        mltl_filename = f"{AT_DIR}int.mltl"

        (status, ft_asm, pt_asm, bz_asm, at_asm, scq_asm) = compile(mltl_filename, csv_filename, enable_at=True, enable_cse=True, enable_extops=True, enable_assemble=False)
        assert status == ReturnCode.SUCCESS.value

        assert len(at_asm) == 2

        instr = at_asm[0]
        assert instr.args[0].name == "i0"
        assert instr.filter == "int"
        assert instr.rel_op.symbol == ">"
        assert instr.compare.name == "5"

        instr = at_asm[1]
        assert instr.args[0].name == "i0"
        assert instr.filter == "int"
        assert instr.rel_op.symbol == ">"
        assert instr.compare.name == "i1"

    def test_float(self):
        csv_filename = f"{AT_DIR}atomic_checker.csv"
        mltl_filename = f"{AT_DIR}float.mltl"

        (status, ft_asm, pt_asm, bz_asm, at_asm, scq_asm) = compile(mltl_filename, csv_filename, enable_at=True, enable_cse=True, enable_extops=True, enable_assemble=False)
        assert status == ReturnCode.SUCCESS.value

        assert len(at_asm) == 2

        instr = at_asm[0]
        assert instr.args[0].name == "f0"
        assert instr.filter == "float"
        assert instr.rel_op.symbol == ">"
        assert instr.compare.name == "5.0"

        instr = at_asm[1]
        assert instr.args[0].name == "f0"
        assert instr.filter == "float"
        assert instr.rel_op.symbol == ">"
        assert instr.compare.name == "f1"

    def test_rate(self):
        csv_filename = f"{AT_DIR}atomic_checker.csv"
        mltl_filename = f"{AT_DIR}rate.mltl"

        (status, ft_asm, pt_asm, bz_asm, at_asm, scq_asm) = compile(mltl_filename, csv_filename, enable_at=True, enable_cse=True, enable_extops=True, enable_assemble=False)
        assert status == ReturnCode.SUCCESS.value

        assert len(at_asm) == 1

        instr = at_asm[0]
        assert len(instr.args) == 1
        assert instr.args[0].name == "f"
        assert instr.filter == "rate"
        assert instr.rel_op.symbol == "<"
        assert instr.compare.name == "5.0"

    def test_abs_diff_angle(self):
        csv_filename = f"{AT_DIR}atomic_checker.csv"
        mltl_filename = f"{AT_DIR}abs_diff_angle.mltl"

        (status, ft_asm, pt_asm, bz_asm, at_asm, scq_asm) = compile(mltl_filename, csv_filename, enable_at=True, enable_cse=True, enable_extops=True, enable_assemble=False)
        assert status == ReturnCode.SUCCESS.value

        assert len(at_asm) == 1

        instr = at_asm[0]
        assert len(instr.args) == 2
        assert instr.args[0].name == "f0"
        assert instr.args[1].name == "f1"
        assert instr.filter == "abs_diff_angle"
        assert instr.rel_op.symbol == "<"
        assert instr.compare.name == "5.0"

    def test_movavg(self):
        csv_filename = f"{AT_DIR}atomic_checker.csv"
        mltl_filename = f"{AT_DIR}movavg.mltl"

        (status, ft_asm, pt_asm, bz_asm, at_asm, scq_asm) = compile(mltl_filename, csv_filename, enable_at=True, enable_cse=True, enable_extops=True, enable_assemble=False)
        assert status == ReturnCode.SUCCESS.value

        assert len(at_asm) == 1

        instr = at_asm[0]
        assert len(instr.args) == 2
        assert instr.args[0].name == "f"
        assert instr.args[1].name == "3"
        assert instr.filter == "movavg"
        assert instr.rel_op.symbol == "<"
        assert instr.compare.name == "5.0"