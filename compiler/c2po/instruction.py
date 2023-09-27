from enum import Enum
from typing import List, Tuple
    
class Instruction():

    def __init__(self):
        super().__init__()

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

    def __init__(self,  op: FTOperator):
        super().__init__()
        self.operator = op.symbol()
        self.opcode = op.opcode()

        self.scq_size = 1


# Past-time instructions
class PTInstruction(Instruction):

    def __init__(self):
        super().__init__()
        self.scq_size = 1


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

    def __init__(self, op: BZOperator, cids: List[int]):
        super().__init__()
        self.operator = op
        self.symbol = op.symbol()
        self.opcode = op.opcode()
        self.child_ids = cids

    def __str__(self) -> str:
        return f"{self.symbol} {' '.join([f'b{id}' for id in self.child_ids])}"


# Atomic Checker instructions
class ATInstruction(Instruction):

    def __init__(self):
        super().__init__()

    