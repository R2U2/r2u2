from enum import Enum
from typing import List, Tuple

from .ast import *
    
class Instruction():

    def __init__(self):
        super().__init__()
        self.id = -1

# Future-time instructions
class FTOperator(Enum):
    NOP       = 0b11111
    CONFIGURE = 0b11110
    LOAD      = 0b11101
    RETURN    = 0b11100
    GLOBALLY  = 0b11010
    UNTIL     = 0b11001
    NOT       = 0b10111
    AND       = 0b10110

    def symbol(self) -> str:
        return self.name.lower()
    
    def opcode(self) -> int:
        return self.value

class FTInstruction(Instruction):

    def __init__(self,  node: C2PONode, op: FTOperator, c: List[Instruction]):
        super().__init__()
        self.node = node
        self.operator = op
        self.children = c
        
    def __str__(self) -> str:
        return f"{self.operator.symbol()} {' '.join([f'n{c.id}' for c in self.children])}"

# Past-time instructions
class PTOperator(Enum):
    NOP          = 0b01111
    CONFIGURE    = 0b01110
    LOAD         = 0b01101
    RETURN       = 0b01100
    ONCE         = 0b01011
    HISTORICALLY = 0b01010
    SINCE        = 0b01001
    NOT          = 0b00111
    AND          = 0b00110
    OR           = 0b00101
    IMPLIES      = 0b00100
    EQUIVALENT   = 0b00000

    def symbol(self) -> str:
        return self.name.lower()
    
    def opcode(self) -> int:
        return self.value

class PTInstruction(Instruction):

    def __init__(self,  node: C2PONode, op: PTOperator, c: List[Instruction]):
        super().__init__()
        self.node = node
        self.operator = op
        self.children = c
        
    def __str__(self) -> str:
        return f"{self.operator.symbol()} {' '.join([f'n{c.id}' for c in self.children])}"


# Booleanizer instructions
class BZOperator(Enum):
    NONE    = 0b000000
    ILOAD   = 0b000001
    FLOAD   = 0b000010
    ICONST  = 0b000011
    FCONST  = 0b000100
    BWNEG   = 0b000101
    BWAND   = 0b000110
    BWOR    = 0b000111
    BWXOR   = 0b001000
    IEQ     = 0b001001
    FEQ     = 0b001010
    INEQ    = 0b001011
    FNEQ    = 0b001100
    IGT     = 0b001101
    FGT     = 0b001110
    IGTE    = 0b001111
    ILT     = 0b010000
    FLT     = 0b010001
    ILTE    = 0b010010
    INEG    = 0b010011
    FNEG    = 0b010100
    IADD    = 0b010101
    FADD    = 0b010110
    ISUB    = 0b010111
    FSUB    = 0b011000
    IMUL    = 0b011001
    FMUL    = 0b011010
    IDIV    = 0b011011
    FDIV    = 0b011100
    MOD     = 0b011101

    def symbol(self) -> str:
        return self.name.lower()
    
    def opcode(self) -> int:
        return self.value

class BZInstruction(Instruction):

    def __init__(self, node: C2PONode, op: BZOperator, c: List[Instruction]):
        super().__init__()
        self.node = node
        self.operator = op
        self.children = c
        
    def __str__(self) -> str:
        return f"{self.operator.symbol()} {' '.join([f'b{c.id}' for c in self.children])}"


# Atomic Checker instructions
class ATCond(Enum):
    EQ  = 0b000
    NEQ = 0b001
    LT  = 0b010
    LEQ = 0b011
    GT  = 0b100
    GEQ = 0b101

class ATFilter(Enum):
    BOOL           = 0b0001
    INT            = 0b0010
    FLOAT          = 0b0011
    FORMULA        = 0b0100
    RATE           = 0b0101
    ABS_DIFF_ANGLE = 0b0110
    MOVAVG         = 0b0111
    EXACTLY_ONE_OF = 0b1000
    NONE_OF        = 0b1001
    ALL_OF         = 0b1010

class ATInstruction(Instruction):

    def __init__(self):
        super().__init__()

# maps (C2PONodeType, is_integer_type, is_future_time) -> Instruction
InstructionTable = Callable[[C2PONode, List[Instruction]], Dict[Tuple[type, bool, bool], Instruction]]

instruction_table: InstructionTable = lambda node, child_instrs: {
    (C2POBool, True, True):    BZInstruction(node, BZOperator.ICONST, child_instrs),
    (C2POInteger, True, True): BZInstruction(node, BZOperator.ICONST, child_instrs),
    (C2POFloat, True, True):   BZInstruction(node, BZOperator.FCONST, child_instrs),
    (C2POBool, True, True):    BZInstruction(node, BZOperator.ICONST, child_instrs)
}


def generate_assembly(
    program: C2POProgram, 
    context: C2POContext
) -> Tuple[List[BZInstruction], List[ATInstruction], List[FTInstruction], List[PTInstruction]]:
    bz_asm: List[BZInstruction] = []
    at_asm: List[ATInstruction] = []
    ft_asm: List[FTInstruction] = []
    pt_asm: List[PTInstruction] = []

    bzid, atid, ftid, ptid = 0, 0, 0, 0

    def generate_assembly_util(node: C2PONode, context: C2POContext) -> Instruction:
        nonlocal bz_asm, at_asm, ft_asm, pt_asm
        nonlocal bzid, atid, ftid, ptid
        instr: Optional[Instruction] = None

        # traverse AST and generate sub-expression instructions
        child_instrs = [generate_assembly_util(c, context) for c in node.get_children()]

        instr = instruction_table(node, child_instrs)[(type(node), True, True)]

        # create this node's corresponding instruction
        if isinstance(node, C2POBool):
            instr = BZInstruction(node, BZOperator.ICONST, child_instrs)
        if isinstance(node, C2POInteger):
            instr = BZInstruction(node, BZOperator.ICONST, child_instrs)
        elif isinstance(node, C2POFloat):
            instr = BZInstruction(node, BZOperator.FCONST, child_instrs)
        elif isinstance(node, C2POSignal) and is_integer_type(node.type):
            instr = BZInstruction(node, BZOperator.ILOAD, child_instrs)
        elif isinstance(node, C2POSignal):
            instr = BZInstruction(node, BZOperator.FLOAD, child_instrs)
        elif isinstance(node, C2POBitwiseAnd):
            instr = BZInstruction(node, BZOperator.BWAND, child_instrs)
        elif isinstance(node, C2POBitwiseOr):
            instr = BZInstruction(node, BZOperator.BWOR, child_instrs)
        elif isinstance(node, C2POBitwiseXor):
            instr = BZInstruction(node, BZOperator.BWXOR, child_instrs)
        # elif isinstance(node, C2POBitwiseShiftLeft):
        #     instr = BZInstruction(node, BZOperator.SHL, child_instrs)
        # elif isinstance(node, C2POBitwiseShiftRight):
        #     instr = BZInstruction(node, BZOperator.SHR, child_instrs)
        elif isinstance(node, C2POBitwiseNegate):
            instr = BZInstruction(node, BZOperator.BWNEG, child_instrs)
        elif isinstance(node, C2POArithmeticAdd) and is_integer_type(node.type):
            instr = BZInstruction(node, BZOperator.IADD, child_instrs)
        elif isinstance(node, C2POArithmeticAdd):
            instr = BZInstruction(node, BZOperator.FADD, child_instrs)
        elif isinstance(node, C2POArithmeticSubtract) and is_integer_type(node.type):
            instr = BZInstruction(node, BZOperator.ISUB, child_instrs)
        elif isinstance(node, C2POArithmeticSubtract):
            instr = BZInstruction(node, BZOperator.FSUB, child_instrs)
        elif isinstance(node, C2POArithmeticMultiply) and is_integer_type(node.type):
            instr = BZInstruction(node, BZOperator.IMUL, child_instrs)
        elif isinstance(node, C2POArithmeticMultiply):
            instr = BZInstruction(node, BZOperator.FMUL, child_instrs)
        elif isinstance(node, C2POArithmeticDivide) and is_integer_type(node.type):
            instr = BZInstruction(node, BZOperator.IDIV, child_instrs)
        elif isinstance(node, C2POArithmeticDivide):
            instr = BZInstruction(node, BZOperator.FDIV, child_instrs)
        elif isinstance(node, C2POArithmeticModulo):
            instr = BZInstruction(node, BZOperator.MOD, child_instrs)
        elif isinstance(node, C2POArithmeticNegate) and is_integer_type(node.type):
            instr = BZInstruction(node, BZOperator.INEG, child_instrs)
        elif isinstance(node, C2POArithmeticNegate):
            instr = BZInstruction(node, BZOperator.FNEG, child_instrs)
        elif isinstance(node, C2POEqual) and is_integer_type(node.get_lhs().type):
            instr = BZInstruction(node, BZOperator.IEQ, child_instrs)
        elif isinstance(node, C2POEqual):
            instr = BZInstruction(node, BZOperator.FEQ, child_instrs)
        elif isinstance(node, C2PONotEqual) and is_integer_type(node.get_lhs().type):
            instr = BZInstruction(node, BZOperator.INEQ, child_instrs)
        elif isinstance(node, C2PONotEqual):
            instr = BZInstruction(node, BZOperator.FNEQ, child_instrs)
        elif isinstance(node, C2POGreaterThan) and is_integer_type(node.get_lhs().type):
            instr = BZInstruction(node, BZOperator.IGT, child_instrs)
        elif isinstance(node, C2POGreaterThan):
            instr = BZInstruction(node, BZOperator.FGT, child_instrs)
        elif isinstance(node, C2POLessThan) and is_integer_type(node.get_lhs().type):
            instr = BZInstruction(node, BZOperator.ILT, child_instrs)
        elif isinstance(node, C2POLessThan):
            instr = BZInstruction(node, BZOperator.FLT, child_instrs)
        elif isinstance(node, C2POGreaterThanOrEqual) and is_integer_type(node.get_lhs().type):
            instr = BZInstruction(node, BZOperator.IGTE, child_instrs)
        elif isinstance(node, C2POGreaterThanOrEqual):
            # Need to document this somewhere: floating-point comparison with equality 
            # is transformed into comparison w/o equality check
            instr = BZInstruction(node, BZOperator.FGT, child_instrs)
        elif isinstance(node, C2POLessThanOrEqual) and is_integer_type(node.get_lhs().type):
            instr = BZInstruction(node, BZOperator.ILTE, child_instrs)
        elif isinstance(node, C2POLessThanOrEqual):
            instr = BZInstruction(node, BZOperator.FLT, child_instrs)
        elif isinstance(node, C2POLogicalAnd) and context.is_future_time():
            instr = FTInstruction(node, FTOperator.AND, child_instrs)
        elif isinstance(node, C2POLogicalAnd) and context.is_past_time():
            instr = PTInstruction(node, PTOperator.AND, child_instrs)
        # elif isinstance(node, C2POLogicalOr) and context.is_future_time():
        #     instr = FTInstruction(node, FTOperator.OR, child_instrs)
        elif isinstance(node, C2POLogicalOr) and context.is_past_time():
            instr = PTInstruction(node, PTOperator.OR, child_instrs)
        # elif isinstance(node, C2POLogicalXor) and context.is_future_time():
        #     instr = FTInstruction(node, FTOperator.XOR, child_instrs)
        # elif isinstance(node, C2POLogicalXor) and context.is_past_time():
        #     instr = PTInstruction(node, PTOperator.XOR, child_instrs)
        # elif isinstance(node, C2POLogicalImplies) and context.is_future_time():
        #     instr = FTInstruction(node, FTOperator.IMPLIES, child_instrs)
        elif isinstance(node, C2POLogicalImplies) and context.is_past_time():
            instr = PTInstruction(node, PTOperator.IMPLIES, child_instrs)
        # elif isinstance(node, C2POLogicalIff) and context.is_future_time():
        #     instr = FTInstruction(node, FTOperator.EQUIVALENT, child_instrs)
        elif isinstance(node, C2POLogicalIff) and context.is_past_time():
            instr = PTInstruction(node, PTOperator.EQUIVALENT, child_instrs)
        else:
            logger.critical(f"Node '{node}' of python type '{type(node)}' invalid for assembly generation.")
            return Instruction()
        
        # add this node's instruction to corresponding assembly list
        # -- add in FT/PT loads as needed
        if isinstance(instr, BZInstruction):
            instr.id = bzid
            bzid += 1
            bz_asm.append(instr)
        elif isinstance(instr, ATInstruction):
            instr.id = atid
            atid += 1
            at_asm.append(instr)
        elif isinstance(instr, FTInstruction):
            if not context.is_future_time():
                logger.critical(f"Generating FTInstruction for past-time assembly.")

            # TODO: check if any child is a BZ/AT instr -- then need to perform a load

            instr.id = ftid
            ftid += 1
            ft_asm.append(instr)
        elif isinstance(instr, PTInstruction):
            if context.is_future_time():
                logger.critical(f"Generating PTInstruction for future-time assembly.")

            # TODO: check if any child is a BZ/AT instr -- then need to perform a load

            instr.id = ptid
            ptid += 1
            pt_asm.append(instr)

        return instr

    context.set_future_time()
    for spec in program.get_future_time_specs():
        generate_assembly_util(spec, context)

    context.set_past_time()
    for spec in program.get_past_time_specs():
        generate_assembly_util(spec, context)

    return (bz_asm, at_asm, ft_asm, pt_asm)
    

    
