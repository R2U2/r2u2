
from enum import Enum
from struct import Struct as CStruct, calcsize
from typing import Union

from .ast import *

# The following values with suffix '_F' are the format strings
# used to construct the c structs. See the documentation of the
# 'struct' package for info:
# https://docs.python.org/3/library/struct.html
ENGINE_TAG_F = "B"

INSTR_SIZE_F = "B"

BZ_ID_F           = "B"
BZ_OPERATOR_F     = "i"
BZ_STORE_ATOMIC_F = "B"
BZ_ATOMIC_ID_F    = "B"
BZ_PARAM_INT_F    = "i"
BZ_PARAM_FLOAT_F  = "d"

# The following three must be of equal size!
# We check for this in check_size() below
AT_VALUE_BOOL_F  = "?xxxxxxx"
AT_VALUE_SIG_F   = "Bxxxxxxx"
AT_VALUE_INT_F   = "q"
AT_VALUE_FLOAT_F = "d"

AT_REL_OP_F = "i"
AT_FILTER_F = "i"
AT_ID_F     = "B"
AT_COMPARE_VALUE_IS_SIGNAL_F = "B"

TL_ID_F           = "I"
TL_OPERATOR_F     = "i"
TL_OPERAND_TYPE_F = "i"
TL_OPERAND_ID_F   = "Bxxx"

def check_sizes():
    import warnings
    mem_ref_size = CStruct("I").size
    if mem_ref_size != 4:
        warnings.warn(f"MLTL memory reference is 32-bit by default, but platform specifies {mem_ref_size} bytes", BytesWarning)

    if len(set([calcsize(f) for f in {AT_VALUE_BOOL_F, AT_VALUE_FLOAT_F, AT_VALUE_SIG_F, AT_VALUE_INT_F}])) > 1:
        warnings.warn(f"Widths for AT value binary encodings not homogeneous.", BytesWarning)

# The following classes define the allowable parameters in an 
# assembly instruction. They are all either Enums or wrappers
# for a basic data type.
# Enum classes are used for things like opcodes.
# Other classes are used for values lie node IDs and constants.
# Each class must implement the following three methods to be valid
# for use in an assembly instruction:
# 1) 'assemble(self) -> bytes'
#    - Used for generating the binary representation of the parameter 
# 2) '__str__(self) -> str'
#    - Used for a human-readable format of the parameter
# 3) '__repr__(self) -> str'
#    - Used for a string format of the binary representation
#
# NOTE: we could use ABCs (https://docs.python.org/3.8/library/abc.html) and
# define 'assemble', '__str__', and '__repr__' as abstract methods, but I just 
# hate decorators.

class EngineTag(Enum):
    NA = 0 # Null instruction tag - acts as ENDSEQ
    SY = 1 # System commands - reserved for monitor control
    CG = 2 # Immediate Configuration Directive
    AT = 3 # Original Atomic Checker
    TL = 4 # MLTL Temporal logic engine
    BZ = 5 # Booleanizer

    def symbol(self) -> str:
        return self.name

    def assemble(self) -> bytes:
        return CStruct(ENGINE_TAG_F).pack(self.value)

    def __str__(self) -> str:
        return f"{self.name:2}"

    def __repr__(self) -> str:
        return f"{self.value:3b}"

class BZId():

    def __init__(self, id: int) -> None:
        self.value = id

    def assemble(self) -> bytes:
        return CStruct(BZ_ID_F).pack(self.value)

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

    def assemble(self) -> bytes:
        return CStruct(BZ_OPERATOR_F).pack(self.value)

    def __str__(self) -> str:
        return super().__str__()

    def __repr__(self) -> str:
        return super().__repr__()

class BZStoreAtomic():

    def __init__(self, value: bool) -> None:
        self.value = value

    def assemble(self) -> bytes:
        return CStruct(BZ_STORE_ATOMIC_F).pack(self.value)

class BZAtomicId():

    def __init__(self, id: int) -> None:
        self.value = id

    def assemble(self) -> bytes:
        return CStruct(BZ_ATOMIC_ID_F).pack(self.value)

class BZParameter():

    def __init__(self, value: Union[int, float]) -> None:
        self.value = value

    def assemble(self) -> bytes:
        if isinstance(self.value, int):
            return CStruct(BZ_PARAM_INT_F).pack(self.value)
        elif isinstance(self.value, float):
            return CStruct(BZ_PARAM_FLOAT_F).pack(self.value)
        raise NotImplementedError

class ATRelOp(Enum):
    EQ   = 0b000
    NEQ  = 0b001
    LT   = 0b010
    LEQ  = 0b011
    GT   = 0b100
    GEQ  = 0b101
    NONE = 0b111

    def symbol(self) -> str:
        return self.name.lower()

    def assemble(self) -> bytes:
        return CStruct(AT_REL_OP_F).pack(self.value)

class ATFilter(Enum):
    NONE           = 0b0000
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

    def symbol(self) -> str:
        return self.name.lower()

    def assemble(self) -> bytes:
        return CStruct(AT_FILTER_F).pack(self.value)

class ATCompareValue():

    def __init__(
        self, 
        value: Union[bool, int, float],
        is_signal: bool
    ) -> None:
        self.value = value
        self.is_signal = is_signal

    def assemble(self) -> bytes:
        if self.is_signal:
            return CStruct(AT_VALUE_SIG_F).pack(self.value) 
        elif isinstance(self.value, bool):
            return CStruct(AT_VALUE_BOOL_F).pack(self.value) 
        elif isinstance(self.value, int):
            return CStruct(AT_VALUE_INT_F).pack(self.value) 
        elif isinstance(self.value, float):
            return CStruct(AT_VALUE_FLOAT_F).pack(self.value) 
        raise NotImplementedError # TODO: replace with error message

class ATCompareIsSignal():

    def __init__(self, value: bool) -> None:
        self.value = value

    def assemble(self) -> bytes:
        return CStruct(AT_VALUE_BOOL_F).pack(self.value)

class ATAuxFilterArg():

    def __init__(self, value: Union[int, float]) -> None:
        self.value = value

    def assemble(self) -> bytes:
        if isinstance(self.value, int):
            return CStruct(AT_VALUE_INT_F).pack(self.value)
        elif isinstance(self.value, float):
            return CStruct(AT_VALUE_FLOAT_F).pack(self.value)
        raise NotImplementedError # TODO: replace with error message

class ATPrimaryFilterArg():

    def __init__(self, value: int) -> None:
        self.value = value

    def assemble(self) -> bytes:
        return CStruct(AT_VALUE_SIG_F).pack(self.value)

class ATId():

    def __init__(self, id: int) -> None:
        self.value = id

    def assemble(self) -> bytes:
        return CStruct(AT_ID_F).pack(self.value)

class TLId():

    def __init__(self, id: int) -> None:
        self.id = id

    def assemble(self) -> bytes:
        return CStruct(TL_ID_F).pack(self.id)

    def __str__(self) -> str:
        return f"{self.id:3}"

    def __repr__(self) -> str:
        return f"{self.id:8b}"

class TLOperandType(Enum):
    DIRECT      = 0b01
    ATOMIC      = 0b00
    SUBFORMULA  = 0b10
    NONE        = 0b11

    def symbol(self) -> str:
        return self.name.lower()

    def assemble(self) -> bytes:
        return CStruct(TL_OPERAND_TYPE_F).pack(self.value)

    def __str__(self) -> str:
        return f"{self.name:10}"

    def __repr__(self) -> str:
        return f"{self.value:2b}"

class TLOperandId():

    def __init__(self, id: int) -> None:
        self.id = id

    def assemble(self) -> bytes:
        return CStruct(TL_OPERAND_ID_F).pack(self.id)

    def __str__(self) -> str:
        return f"{self.id:5}"

    def __repr__(self) -> str:
        return f"{self.id:8b}"

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

    def is_temporal(self) -> bool:
        return self is FTOperator.GLOBALLY or self is FTOperator.UNTIL

    def is_load(self) -> bool:
        return self is FTOperator.LOAD

    def assemble(self) -> bytes:
        return CStruct(TL_OPERATOR_F).pack(self.value)

    def __str__(self) -> str:
        return f"{self.name:12}"

    def __repr__(self) -> str:
        return f"{self.value:5b}"

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

    def assemble(self) -> bytes:
        return CStruct(TL_OPERATOR_F).pack(self.value)

    def __str__(self) -> str:
        return f"{self.name:12}"

    def __repr__(self) -> str:
        return f"{self.value:5b}"
    
Operator = Union[FTOperator, PTOperator, BZOperator]
TLOperator = Union[FTOperator, PTOperator]

class Instruction():

    def __init__(self) -> None:
        self.fields = ()

    def __str__(self) -> str:
        return " ".join([str(f) for f in self.fields])

    def __repr__(self) -> str:
        return " ".join([repr(f) for f in self.fields])

class BZInstruction(Instruction):

    def __init__(
        self, 
        id: int, 
        operator: BZOperator, 
        store_atomic: bool,
        atomic_id: int,
        param1: Union[int, float],
        param2: Union[int, float]
    ):
        self.fields = (
            EngineTag.BZ, 
            BZId(id),
            operator,
            BZStoreAtomic(store_atomic),
            BZAtomicId(atomic_id),
            BZParameter(param1),
            BZParameter(param2)
        )

    def assemble(self) -> bytes:
        # Note: This method could be place in the parent class
        # Instruction since it's identical across all subclasses
        # of Instruction -- we don't do this so that the type checker
        # enforces that every field implements 'assemble()'.
        binary = bytes()
        for field in self.fields:
            binary += field.assemble()
        instr_size = CStruct(INSTR_SIZE_F).pack(binary)
        return instr_size + binary

class ATInstruction(Instruction):

    def __init__(
        self, 
        id: int, 
        filter: ATFilter, 
        rel_op: ATRelOp,
        primary_filter_arg: int,
        aux_filter_arg: Union[int, float],
        compare_value: Union[bool, int, float],
        compare_value_is_sig: bool
    ):
        self.fields = (
            EngineTag.AT, 
            ATCompareValue(compare_value, compare_value_is_sig),
            ATAuxFilterArg(aux_filter_arg),
            rel_op,
            filter,
            ATPrimaryFilterArg(primary_filter_arg),
            ATId(id), 
            ATCompareIsSignal(compare_value_is_sig),
            ATId(id)
        )

    def assemble(self) -> bytes:
        # Note: This method could be place in the parent class
        # Instruction since it's identical across all subclasses
        # of Instruction -- we don't do this so that the type checker
        # enforces that every field implements 'assemble()'.
        binary = bytes()
        for field in self.fields:
            binary += field.assemble()
        instr_size = CStruct(INSTR_SIZE_F).pack(binary)
        return instr_size + binary

class TLInstruction(Instruction):

    def __init__(
        self, 
        id: int, 
        operator: TLOperator, 
        opnd1_type: TLOperandType, opnd1_id: int, 
        opnd2_type: TLOperandType, opnd2_id: int
    ):
        self.fields = (
            EngineTag.TL, 
            opnd1_type, TLOperandId(opnd1_id),
            opnd2_type, TLOperandId(opnd2_id),
            TLId(id), 
            operator
        )

    def assemble(self) -> bytes:
        # Note: This method could be place in the parent class
        # Instruction since it's identical across all subclasses
        # of Instruction -- we don't do this so that the type checker
        # enforces that every field implements 'assemble()'.
        binary = bytes()
        for field in self.fields:
            binary += field.assemble()
        instr_size = CStruct(INSTR_SIZE_F).pack(binary)
        return instr_size + binary


def generate_assembly(
    program: C2POProgram,
    context: C2POContext
) -> List[Instruction]:
    bzid, atid, ftid, ptid = 0, 0, 0, 0

    instr_dict: Dict[C2PONode, Instruction] = {}
    instr_list = List[Instruction]

    def generate_assembly_util(node: C2PONode):

        if not isinstance(node, C2POExpression):
            return

        # if isinstance(node, C2POAtomicChecker):
        #     instr = ATInstruction(atid, context.atomic_checkers[node.symbol])
        # elif isinstance(node, C2POBool):
        #     instr = BZInstruction(node, BZOperator.ICONST, child_instrs)
        # elif isinstance(node, C2POInteger):
        #     instr = BZInstruction(node, BZOperator.ICONST, child_instrs)
        # elif isinstance(node, C2POFloat):
        #     instr = BZInstruction(node, BZOperator.FCONST, child_instrs)
        # elif isinstance(node, C2POSignal) and is_integer_type(node.type):
        #     instr = BZInstruction(node, BZOperator.ILOAD, child_instrs)
        # elif isinstance(node, C2POSignal):
        #     instr = BZInstruction(node, BZOperator.FLOAD, child_instrs)
        # elif isinstance(node, C2POBitwiseAnd):
        #     instr = BZInstruction(node, BZOperator.BWAND, child_instrs)
        # elif isinstance(node, C2POBitwiseOr):
        #     instr = BZInstruction(node, BZOperator.BWOR, child_instrs)
        # elif isinstance(node, C2POBitwiseXor):
        #     instr = BZInstruction(node, BZOperator.BWXOR, child_instrs)


    return []


def assemble(
    program: C2POProgram,
    context: C2POContext,
    quiet: bool
) -> bytes:
    check_sizes()
    return bytes()