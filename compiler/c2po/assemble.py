from enum import Enum
from struct import Struct as cStruct
from typing import List, Optional, Tuple

from .logger import Color
from .ast import *

class ENGINE_TAGS(Enum):
    NA = 0 # Null instruction tag - acts as ENDSEQ
    SY = 1 # System commands - reserved for monitor control
    CG = 2 # Immediate Configuration Directive
    AT = 3 # Original Atomic Checker
    TL = 4 # MLTL Temporal logic engine
    BZ = 5 # Booleanizer

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

    def is_constant(self) -> bool:
        return self is BZOperator.ICONST or self is BZOperator.FCONST
    
    def is_load(self) -> bool:
        return self is BZOperator.ILOAD or self is BZOperator.FLOAD

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

class TLOperandType(Enum):
    DIRECT      = 0b01
    ATOMIC      = 0b00
    SUBFORMULA  = 0b10
    NOT_SET     = 0b11

class FTOperator(Enum):
    NOP       = 0b11111
    CONFIGURE = 0b11110
    LOAD      = 0b11101
    RETURN    = 0b11100
    GLOBAL    = 0b11010
    UNTIL     = 0b11001
    NOT       = 0b10111
    AND       = 0b10110

    def symbol(self) -> str:
        return self.name.lower()
    
    def opcode(self) -> int:
        return self.value

    def is_temporal(self) -> bool:
        return self is FTOperator.GLOBAL or self is FTOperator.UNTIL

    def is_load(self) -> bool:
        return self is FTOperator.LOAD

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

    def is_temporal(self) -> bool:
        return self == PTOperator.ONCE or self == PTOperator.HISTORICALLY or self == PTOperator.SINCE

    def is_load(self) -> bool:
        return self is PTOperator.LOAD
    
Operator = Union[FTOperator, PTOperator, BZOperator]
TLOperator = Union[FTOperator, PTOperator]


class Instruction():

    def __init__(self, node: C2POExpression):
        super().__init__()
        self.node = node
        self.operator: Optional[Operator] = None
        self.id = -1

    def id_str(self) -> str:
        return f"ERR"

    def assemble(self) -> bytes:
        return bytes()


class BZInstruction(Instruction):

    def __init__(self, node: C2POExpression, op: BZOperator, c: List[Instruction]):
        super().__init__(node)
        self.operator: BZOperator = op
        self.children = c

    def id_str(self) -> str:
        if isinstance(self.node, C2POBool):
            return f"{self.node.value}"
        return f"b{self.id}"
        
    def __str__(self) -> str:
        if isinstance(self.node, C2POSignal):
            return f"b{self.id} {self.operator.symbol()} s{self.node.signal_id}"
        elif isinstance(self.node, C2POConstant):
            return f"b{self.id} {self.operator.symbol()} {self.node.value}"
        return f"b{self.id} {self.operator.symbol()} {' '.join([f'b{c.id}' for c in self.children])}"

    def assemble(self) -> bytes:
        param1: Optional[Union[int,float]] = None
        param2: Optional[int] = None

        if isinstance(self.node, C2POSignal):
            param1 = self.node.signal_id
            param2 = 0
        elif isinstance(self.node, C2POConstant):
            param1 = self.node.value
            param2 = 0
        elif len(self.children) == 1:
            param1 = self.children[0].id
            param2 = 0
        elif len(self.children) == 2:
            param1 = self.children[0].id
            param2 = self.children[1].id
        else:
            logger.error(f"{self.node.ln}: Error in generating assembly for `{self.node}`.")
            return bytes()

        instr_format = cStruct("BiBBqq") if isinstance(param1, int) else  cStruct("BiBBdq")

        engine_tag_bytes = cStruct("B").pack(ENGINE_TAGS.BZ.value)
        instr_bytes = instr_format.pack(
            self.id, 
            self.operator.value, 
            self.node.atomic_id > -1, 
            self.node.atomic_id if self.node.atomic_id > -1 else 0,
            param1, 
            param2
        )
        
        return engine_tag_bytes + instr_bytes


class ATInstruction(Instruction):

    def __init__(self, node: C2POExpression):
        super().__init__(node)

    def assemble(self) -> bytes:
        return bytes()


class TLInstruction(Instruction):

    def __init__(self, node: C2POExpression, op: TLOperator, c: List[Instruction]):
        super().__init__(node)
        self.operator: TLOperator = op
        self.children = c

    def id_str(self) -> str:
        return f"n{self.id}"

    def assemble(self) -> bytes:
        operand_1: Tuple[TLOperandType, int] = (TLOperandType.NOT_SET, 0)
        operand_2: Tuple[TLOperandType, int] = (TLOperandType.NOT_SET, 0)

        if self.operator.is_load():
            operand_1 = (TLOperandType.ATOMIC, self.children[0].node.atomic_id)
        elif len(self.children) > 0 and isinstance(self.children[0].node, C2POBool):
            operand_1 = (TLOperandType.DIRECT, self.children[0].node.value)
        elif len(self.children) > 0:
            operand_1 = (TLOperandType.SUBFORMULA, self.children[0].id)

        if isinstance(self.node, C2POSpecification):
            operand_2 = (TLOperandType.DIRECT, self.node.formula_number)
        elif len(self.children) > 1 and isinstance(self.children[1].node, C2POBool):
            operand_2 = (TLOperandType.DIRECT, self.children[1].node.value)
        elif len(self.children) > 1:
            operand_2 = (TLOperandType.SUBFORMULA, self.children[1].id)

        operand_format = cStruct("iBxxx")
        instr_format = cStruct(f"{operand_format.size}s{operand_format.size}sIi")

        # print(f"FT Assembled:\n\t({operand_1[0]}, {operand_1[1]})\n\t({operand_2[0]}, {operand_2[1]})\n\t{self.id}\n\t{self.operator}")

        engine_tag_bytes = cStruct("B").pack(ENGINE_TAGS.TL.value)
        instr_bytes = instr_format.pack(
            operand_format.pack(operand_1[0].value, operand_1[1]),
            operand_format.pack(operand_2[0].value, operand_2[1]),
            self.id, 
            self.operator.value
        )

        return engine_tag_bytes + instr_bytes
        
    def __str__(self) -> str:
        if self.operator is FTOperator.LOAD or self.operator is PTOperator.LOAD:
            return f"n{self.id} {self.operator.symbol()} {self.children[0].id_str()}"
        elif self.operator.is_temporal():
            temp = cast(C2POTemporalOperator, self.node)
            return f"n{self.id} {self.operator.symbol()} {temp.interval.lb} {temp.interval.ub} {' '.join([f'{c.id_str()}' for c in self.children])}"
        return f"n{self.id} {self.operator.symbol()} {' '.join([f'{c.id_str()}' for c in self.children])}"


class FTInstruction(TLInstruction):

    def __init__(self, node: C2POExpression, op: FTOperator, c: List[Instruction]):
        super().__init__(node, op, c)

    def assemble_scq(self, scq_asm: Tuple[int, int]) -> bytes:
        engine_tag_bytes = cStruct("BB").pack(ENGINE_TAGS.CG.value, ENGINE_TAGS.TL.value)

        operand_format = cStruct("iBxxx")
        instr_format = cStruct(f"{operand_format.size}s{operand_format.size}sIi")

        (start_pos, end_pos) = scq_asm

        # add SCQ information
        instr_bytes = engine_tag_bytes + instr_format.pack(
            operand_format.pack(TLOperandType.SUBFORMULA.value, self.id),
            operand_format.pack(TLOperandType.DIRECT.value, end_pos - start_pos),
            start_pos, 
            FTOperator.CONFIGURE.value
        )

        # print(f"SCQ Assembled (n{self.id}) ({self.node}):\n\t({TLOperandType.SUBFORMULA}, {self.id})\n\t({TLOperandType.DIRECT}, {end_pos - start_pos})\n\t{start_pos}\n\t{FTOperator.CONFIGURE}")

        if self.operator.is_temporal():
            temp = cast(C2POTemporalOperator, self.node)

            # add lower bound
            instr_bytes += engine_tag_bytes + instr_format.pack(
                operand_format.pack(TLOperandType.SUBFORMULA.value, self.id),
                operand_format.pack(TLOperandType.ATOMIC.value, 0),
                temp.interval.lb, 
                FTOperator.CONFIGURE.value
            )

            # print(f"\t({TLOperandType.SUBFORMULA}, {self.id})\n\t({TLOperandType.ATOMIC}, {0})\n\t{temp.interval.lb}\n\t{FTOperator.CONFIGURE}")

            # add upper bound
            instr_bytes += engine_tag_bytes + instr_format.pack(
                operand_format.pack(TLOperandType.SUBFORMULA.value, self.id),
                operand_format.pack(TLOperandType.ATOMIC.value, 1),
                temp.interval.ub, 
                FTOperator.CONFIGURE.value
            )

            # print(f"\t({TLOperandType.SUBFORMULA}, {self.id})\n\t({TLOperandType.ATOMIC}, {1})\n\t{temp.interval.ub}\n\t{FTOperator.CONFIGURE}")

        return instr_bytes


class PTInstruction(TLInstruction):

    def __init__(self, node: C2POExpression, op: PTOperator, c: List[Instruction]):
        super().__init__(node, op, c)

    def assemble_boxq(self, num_boxqs: int) -> bytes:
        if not self.operator.is_temporal():
            return b""

        engine_tag_bytes = cStruct("BB").pack(ENGINE_TAGS.CG.value, ENGINE_TAGS.TL.value)

        operand_format = cStruct("iBxxx")
        instr_format = cStruct(f"{operand_format.size}s{operand_format.size}sIi")
        
        temp = cast(C2POTemporalOperator, self.node)

        instr_bytes = engine_tag_bytes + instr_format.pack(
            operand_format.pack(TLOperandType.SUBFORMULA.value, self.id),
            operand_format.pack(TLOperandType.DIRECT.value, 64),
            64 * num_boxqs, 
            FTOperator.CONFIGURE.value
        )
        instr_bytes += engine_tag_bytes + instr_format.pack(
            operand_format.pack(TLOperandType.SUBFORMULA.value, self.id),
            operand_format.pack(TLOperandType.ATOMIC.value, 0),
            temp.interval.lb, 
            FTOperator.CONFIGURE.value
        )
        instr_bytes += engine_tag_bytes + instr_format.pack(
            operand_format.pack(TLOperandType.SUBFORMULA.value, self.id),
            operand_format.pack(TLOperandType.ATOMIC.value, 1),
            temp.interval.ub, 
            FTOperator.CONFIGURE.value
        )

        return instr_bytes



# Alternative approach for mapping nodes to their respective instructions
# maps (C2PONodeType, is_integer_type, is_future_time) -> Instruction
# InstructionTable = Callable[[C2PONode, List[Instruction]], Dict[Tuple[type, bool, bool], Instruction]]
# 
# instruction_table: InstructionTable = lambda node, child_instrs: {
#     (C2POBool, True, True):    BZInstruction(node, BZOperator.ICONST, child_instrs),
#     (C2POInteger, True, True): BZInstruction(node, BZOperator.ICONST, child_instrs),
#     (C2POFloat, True, True):   BZInstruction(node, BZOperator.FCONST, child_instrs),
#     (C2POBool, True, True):    BZInstruction(node, BZOperator.ICONST, child_instrs)
# }
# 
# The call would look something like:
# instr = instruction_table(node, child_instrs)[(type(node), is_integer_type(node.type), context.is_future_time())]


def generate_aliases(program: C2POProgram, context: C2POContext) -> List[str]:
    """Generates strings corresponding to the alias file for the argument program. The alias file is used by R2U2 to print formula labels and contract status."""
    s: List[str] = []

    for spec_section in [s for s in program.get_spec_sections()]:
        for spec in [s for s in spec_section.get_specs() if isinstance(s, C2POSpecification)]:
            s.append(f"F {spec.symbol} {spec.formula_number}")

    for contract in context.contracts.values():
        (f1, f2, f3) =  contract.formula_numbers
        s.append(f"C {contract.symbol} {f1} {f2} {f3}")

    return s


def generate_instruction_assembly(
    program: C2POProgram, 
    context: C2POContext
) -> Tuple[List[BZInstruction], List[ATInstruction], List[FTInstruction], List[PTInstruction]]:
    bz_asm: List[BZInstruction] = []
    at_asm: List[ATInstruction] = []
    ft_asm: List[FTInstruction] = []
    pt_asm: List[PTInstruction] = []

    bzid, atid, ftid, ptid = 0, 0, 0, 0

    instructions: Dict[C2PONode, Union[Instruction, Tuple[Instruction, Instruction]]] = {}

    def generate_instruction_assembly_util(node: C2PONode):
        nonlocal bz_asm, at_asm, ft_asm, pt_asm
        nonlocal bzid, atid, ftid, ptid
        nonlocal instructions
        nonlocal context

        if not isinstance(node, C2POExpression):
            return

        instr: Optional[Instruction] = None

        # collect child instructions 
        # -- they might be a (load,instr) or just an instr
        child_instrs = []
        for child in [instructions[c] for c in node.get_children() if c in instructions]:
            if not isinstance(child, tuple):
                child_instrs.append(child)
            elif node.engine == R2U2Engine.TEMPORAL_LOGIC: 
                # then child is an atomic, we have to load it
                (tl_load_instr, _) = child
                child_instrs.append(tl_load_instr)
            else:
                # then child is an atomic, but we are BZ/AT
                (_, child_instr) = child
                child_instrs.append(child_instr)

        # create this node"s corresponding instruction
        if isinstance(node, C2POBool):
            instr = BZInstruction(node, BZOperator.ICONST, child_instrs)
        elif isinstance(node, C2POInteger):
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
        elif isinstance(node, C2POLogicalNegate) and context.is_future_time():
            instr = FTInstruction(node, FTOperator.NOT, child_instrs)
        elif isinstance(node, C2POLogicalNegate) and context.is_past_time():
            instr = PTInstruction(node, PTOperator.NOT, child_instrs)
        elif isinstance(node, C2POGlobal) and context.is_future_time():
            instr = FTInstruction(node, FTOperator.GLOBAL, child_instrs)
        # elif isinstance(node, C2POFuture) and context.is_future_time():
        #     instr = FTInstruction(node, FTOperator.FUTURE, child_instrs)
        elif isinstance(node, C2POUntil) and context.is_future_time():
            instr = FTInstruction(node, FTOperator.UNTIL, child_instrs)
        # elif isinstance(node, C2PORelease) and context.is_future_time():
        #     instr = FTInstruction(node, FTOperator.RELEASE, child_instrs)
        elif isinstance(node, C2POSince) and context.is_past_time():
            instr = PTInstruction(node, PTOperator.SINCE, child_instrs)
        elif isinstance(node, C2POHistorical) and context.is_past_time():
            instr = PTInstruction(node, PTOperator.HISTORICALLY, child_instrs)
        elif isinstance(node, C2POOnce) and context.is_past_time():
            instr = PTInstruction(node, PTOperator.ONCE, child_instrs)
        elif isinstance(node, C2POSpecification) and context.is_future_time():
            instr = FTInstruction(node, FTOperator.RETURN, child_instrs)
        elif isinstance(node, C2POSpecification) and context.is_past_time():
            instr = PTInstruction(node, PTOperator.RETURN, child_instrs)
        else:
            logger.critical(f"Node '{node}' of python type '{type(node)}' invalid for assembly generation.")
            return Instruction(node)

        # add in load instructions for atomics in the TL assemblies
        load_instr: Optional[Instruction] = None
        if node in context.atomics and context.is_future_time():
            load_instr = FTInstruction(node, FTOperator.LOAD, [instr])
            load_instr.id = ftid
            ftid += 1
            ft_asm.append(load_instr)
        elif node in context.atomics and context.is_past_time():
            load_instr = PTInstruction(node, PTOperator.LOAD, [instr])
            load_instr.id = ptid
            ptid += 1
            pt_asm.append(load_instr)

        if load_instr:
            instructions[node] = (load_instr, instr)
        else:
            instructions[node] = instr

        # add this node"s instruction to corresponding assembly list
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
            instr.id = ftid
            ftid += 1
            ft_asm.append(instr)
        elif isinstance(instr, PTInstruction):
            if context.is_future_time():
                logger.critical(f"Generating PTInstruction for future-time assembly.")
            instr.id = ptid
            ptid += 1
            pt_asm.append(instr)

    context.set_future_time()
    for spec in program.get_future_time_specs():
        postorder(spec, generate_instruction_assembly_util)

    context.set_past_time()
    for spec in program.get_past_time_specs():
        postorder(spec, generate_instruction_assembly_util)

    return (bz_asm, at_asm, ft_asm, pt_asm)


def generate_scq_assembly(
    program: C2POProgram, 
    context: C2POContext
) -> List[Tuple[int,int]]:
    ret: List[Tuple[int,int]] = []
    pos: int = 0

    def gen_scq_assembly_util(a: C2PONode) :
        nonlocal ret, pos

        if a.scq_size < 0:
            return

        start_pos = pos
        end_pos = start_pos + a.scq_size
        pos = end_pos
        ret.append((start_pos,end_pos))

    for spec in program.get_specs():
        postorder(spec, gen_scq_assembly_util)

    return ret


def print_assembly(
    aliases: List[str],
    bz_asm: List[BZInstruction], 
    at_asm: List[ATInstruction],
    ft_asm: List[FTInstruction], 
    pt_asm: List[PTInstruction],
    scq_asm: List[Tuple[int,int]]
):
    print(Color.HEADER+"AT Assembly"+Color.ENDC+":")
    [print(f"\t{s}") for s in at_asm]
    print(Color.HEADER+"BZ Assembly"+Color.ENDC+":")
    [print(f"\t{s}") for s in bz_asm]
    print(Color.HEADER+"FT Assembly"+Color.ENDC+":")
    [print(f"\t{s}") for s in ft_asm]
    print(Color.HEADER+"PT Assembly"+Color.ENDC+":")
    [print(f"\t{s}") for s in pt_asm]
    print(Color.HEADER+"SCQ Assembly"+Color.ENDC+":")
    [print(f"\t{s}") for s in scq_asm]
    print(Color.HEADER+"Aliases"+Color.ENDC+":")
    [print(f"\t{s}") for s in aliases]


def assemble(program: C2POProgram, context: C2POContext, quiet: bool) -> bytes:
    # Generate assembly
    aliases = generate_aliases(program, context)
    (bz_asm, at_asm, ft_asm, pt_asm) = generate_instruction_assembly(program, context)
    scq_asm: List[Tuple[int,int]] = generate_scq_assembly(program, context)

    if not quiet:
        print_assembly(aliases, bz_asm, at_asm, ft_asm, pt_asm, scq_asm)

    # Build up the spec binary
    spec_bytearray = bytearray()
    spec_header = b"C2P0 Version 1.0.0 for R2U2 V3\x00"
    spec_bytearray.extend(cStruct("B").pack(len(spec_header)+1) + spec_header)

    for instr in bz_asm + at_asm + ft_asm + pt_asm:
        instr_bytes = instr.assemble()
        spec_bytearray.extend(cStruct("B").pack(len(instr_bytes)+1) + instr_bytes)

    # Configure SCQ size and, if temporal, interval bounds
    for instr in ft_asm:
        instr_bytes = instr.assemble_scq(scq_asm[instr.id])
        spec_bytearray.extend(cStruct("B").pack(len(instr_bytes)+1) + instr_bytes)

    # Configure box queues for temporal PT nodes
    boxqs = 1
    for instr in pt_asm:
        instr_bytes = instr.assemble_boxq(boxqs)
        boxqs += 1
        spec_bytearray.extend(cStruct("B").pack(len(instr_bytes)+1) + instr_bytes)

    spec_bytearray.extend(b"\x00") # End of instruction segment

    # Configure aliases
    for alias in aliases:
        spec_bytearray.extend(alias.encode("ascii") + b"\x00")
    
    spec_bytearray.extend(b"\x00") # End of aux defs segment

    return spec_bytearray
