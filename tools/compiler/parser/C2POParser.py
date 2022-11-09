# Generated from C2PO.g by ANTLR 4.11.1
# encoding: utf-8
from antlr4 import *
from io import StringIO
import sys
if sys.version_info[1] > 5:
	from typing import TextIO
else:
	from typing.io import TextIO

def serializedATN():
    return [
        4,1,75,291,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,2,6,7,
        6,2,7,7,7,2,8,7,8,2,9,7,9,2,10,7,10,2,11,7,11,2,12,7,12,2,13,7,13,
        2,14,7,14,2,15,7,15,2,16,7,16,2,17,7,17,2,18,7,18,2,19,7,19,2,20,
        7,20,2,21,7,21,2,22,7,22,2,23,7,23,2,24,7,24,1,0,1,0,1,0,1,0,5,0,
        55,8,0,10,0,12,0,58,9,0,1,1,1,1,4,1,62,8,1,11,1,12,1,63,1,2,1,2,
        1,2,1,2,4,2,70,8,2,11,2,12,2,71,1,2,1,2,1,2,1,3,1,3,4,3,79,8,3,11,
        3,12,3,80,1,3,3,3,84,8,3,1,4,1,4,1,4,5,4,89,8,4,10,4,12,4,92,9,4,
        1,4,1,4,1,4,1,4,1,5,1,5,1,5,1,5,1,5,5,5,103,8,5,10,5,12,5,106,9,
        5,1,5,1,5,1,6,1,6,1,6,1,6,1,6,1,6,1,6,1,6,1,6,1,6,1,6,3,6,121,8,
        6,1,7,1,7,4,7,125,8,7,11,7,12,7,126,1,8,1,8,1,8,1,8,1,8,1,9,1,9,
        4,9,136,8,9,11,9,12,9,137,1,10,1,10,1,10,1,10,1,10,1,10,1,10,3,10,
        147,8,10,1,10,1,10,1,10,3,10,152,8,10,1,11,1,11,1,11,1,11,1,12,1,
        12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,3,12,171,
        8,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,
        1,12,1,12,1,12,3,12,188,8,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,
        1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,
        1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,
        1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,
        1,12,1,12,1,12,1,12,5,12,240,8,12,10,12,12,12,243,9,12,1,13,1,13,
        1,13,3,13,248,8,13,1,13,3,13,251,8,13,1,14,1,14,1,14,1,14,1,15,1,
        15,1,15,1,15,3,15,261,8,15,1,15,1,15,1,16,1,16,1,16,5,16,268,8,16,
        10,16,12,16,271,9,16,1,17,1,17,1,17,1,18,1,18,1,18,1,19,1,19,1,20,
        1,20,1,21,1,21,1,22,1,22,1,23,1,23,1,24,1,24,1,24,0,1,24,25,0,2,
        4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,
        0,8,3,0,50,51,54,54,57,57,2,0,53,53,55,56,2,0,28,29,71,73,1,0,36,
        37,1,0,38,41,1,0,42,43,1,0,44,46,2,0,30,30,43,43,308,0,56,1,0,0,
        0,2,59,1,0,0,0,4,65,1,0,0,0,6,76,1,0,0,0,8,85,1,0,0,0,10,97,1,0,
        0,0,12,120,1,0,0,0,14,122,1,0,0,0,16,128,1,0,0,0,18,133,1,0,0,0,
        20,151,1,0,0,0,22,153,1,0,0,0,24,187,1,0,0,0,26,250,1,0,0,0,28,252,
        1,0,0,0,30,256,1,0,0,0,32,264,1,0,0,0,34,272,1,0,0,0,36,275,1,0,
        0,0,38,278,1,0,0,0,40,280,1,0,0,0,42,282,1,0,0,0,44,284,1,0,0,0,
        46,286,1,0,0,0,48,288,1,0,0,0,50,55,3,2,1,0,51,55,3,6,3,0,52,55,
        3,14,7,0,53,55,3,18,9,0,54,50,1,0,0,0,54,51,1,0,0,0,54,52,1,0,0,
        0,54,53,1,0,0,0,55,58,1,0,0,0,56,54,1,0,0,0,56,57,1,0,0,0,57,1,1,
        0,0,0,58,56,1,0,0,0,59,61,5,16,0,0,60,62,3,4,2,0,61,60,1,0,0,0,62,
        63,1,0,0,0,63,61,1,0,0,0,63,64,1,0,0,0,64,3,1,0,0,0,65,66,5,71,0,
        0,66,67,5,1,0,0,67,69,5,2,0,0,68,70,3,8,4,0,69,68,1,0,0,0,70,71,
        1,0,0,0,71,69,1,0,0,0,71,72,1,0,0,0,72,73,1,0,0,0,73,74,5,3,0,0,
        74,75,5,4,0,0,75,5,1,0,0,0,76,78,5,17,0,0,77,79,3,8,4,0,78,77,1,
        0,0,0,79,80,1,0,0,0,80,78,1,0,0,0,80,81,1,0,0,0,81,83,1,0,0,0,82,
        84,3,10,5,0,83,82,1,0,0,0,83,84,1,0,0,0,84,7,1,0,0,0,85,90,5,71,
        0,0,86,87,5,5,0,0,87,89,5,71,0,0,88,86,1,0,0,0,89,92,1,0,0,0,90,
        88,1,0,0,0,90,91,1,0,0,0,91,93,1,0,0,0,92,90,1,0,0,0,93,94,5,1,0,
        0,94,95,3,12,6,0,95,96,5,4,0,0,96,9,1,0,0,0,97,98,5,20,0,0,98,99,
        5,1,0,0,99,104,5,71,0,0,100,101,5,5,0,0,101,103,5,71,0,0,102,100,
        1,0,0,0,103,106,1,0,0,0,104,102,1,0,0,0,104,105,1,0,0,0,105,107,
        1,0,0,0,106,104,1,0,0,0,107,108,5,4,0,0,108,11,1,0,0,0,109,121,5,
        71,0,0,110,111,5,21,0,0,111,112,5,6,0,0,112,113,3,12,6,0,113,114,
        5,7,0,0,114,121,1,0,0,0,115,116,5,21,0,0,116,117,5,41,0,0,117,118,
        3,12,6,0,118,119,5,40,0,0,119,121,1,0,0,0,120,109,1,0,0,0,120,110,
        1,0,0,0,120,115,1,0,0,0,121,13,1,0,0,0,122,124,5,18,0,0,123,125,
        3,16,8,0,124,123,1,0,0,0,125,126,1,0,0,0,126,124,1,0,0,0,126,127,
        1,0,0,0,127,15,1,0,0,0,128,129,5,71,0,0,129,130,5,8,0,0,130,131,
        3,24,12,0,131,132,5,4,0,0,132,17,1,0,0,0,133,135,5,19,0,0,134,136,
        3,20,10,0,135,134,1,0,0,0,136,137,1,0,0,0,137,135,1,0,0,0,137,138,
        1,0,0,0,138,19,1,0,0,0,139,140,5,71,0,0,140,141,5,1,0,0,141,142,
        3,22,11,0,142,143,5,4,0,0,143,152,1,0,0,0,144,145,5,71,0,0,145,147,
        5,1,0,0,146,144,1,0,0,0,146,147,1,0,0,0,147,148,1,0,0,0,148,149,
        3,24,12,0,149,150,5,4,0,0,150,152,1,0,0,0,151,139,1,0,0,0,151,146,
        1,0,0,0,152,21,1,0,0,0,153,154,3,24,12,0,154,155,5,9,0,0,155,156,
        3,24,12,0,156,23,1,0,0,0,157,158,6,12,-1,0,158,188,3,26,13,0,159,
        160,5,71,0,0,160,161,5,10,0,0,161,162,3,28,14,0,162,163,5,11,0,0,
        163,164,5,10,0,0,164,165,3,24,12,0,165,166,5,11,0,0,166,188,1,0,
        0,0,167,168,5,71,0,0,168,170,5,10,0,0,169,171,3,32,16,0,170,169,
        1,0,0,0,170,171,1,0,0,0,171,172,1,0,0,0,172,188,5,11,0,0,173,174,
        5,43,0,0,174,188,3,24,12,19,175,176,5,42,0,0,176,188,3,24,12,18,
        177,178,5,30,0,0,178,188,3,24,12,17,179,180,3,34,17,0,180,181,3,
        24,12,6,181,188,1,0,0,0,182,183,5,10,0,0,183,184,3,24,12,0,184,185,
        5,11,0,0,185,188,1,0,0,0,186,188,3,38,19,0,187,157,1,0,0,0,187,159,
        1,0,0,0,187,167,1,0,0,0,187,173,1,0,0,0,187,175,1,0,0,0,187,177,
        1,0,0,0,187,179,1,0,0,0,187,182,1,0,0,0,187,186,1,0,0,0,188,241,
        1,0,0,0,189,190,10,16,0,0,190,191,3,46,23,0,191,192,3,24,12,17,192,
        240,1,0,0,0,193,194,10,15,0,0,194,195,3,44,22,0,195,196,3,24,12,
        16,196,240,1,0,0,0,197,198,10,14,0,0,198,199,5,34,0,0,199,240,3,
        24,12,15,200,201,10,13,0,0,201,202,5,35,0,0,202,240,3,24,12,14,203,
        204,10,12,0,0,204,205,3,42,21,0,205,206,3,24,12,13,206,240,1,0,0,
        0,207,208,10,11,0,0,208,209,3,40,20,0,209,210,3,24,12,12,210,240,
        1,0,0,0,211,212,10,10,0,0,212,213,5,31,0,0,213,240,3,24,12,11,214,
        215,10,9,0,0,215,216,5,33,0,0,216,240,3,24,12,10,217,218,10,8,0,
        0,218,219,5,32,0,0,219,240,3,24,12,9,220,221,10,7,0,0,221,222,3,
        36,18,0,222,223,3,24,12,8,223,240,1,0,0,0,224,225,10,5,0,0,225,226,
        5,23,0,0,226,240,3,24,12,6,227,228,10,4,0,0,228,229,5,24,0,0,229,
        240,3,24,12,5,230,231,10,3,0,0,231,232,5,13,0,0,232,233,3,24,12,
        0,233,234,5,1,0,0,234,235,3,24,12,4,235,240,1,0,0,0,236,237,10,20,
        0,0,237,238,5,12,0,0,238,240,5,71,0,0,239,189,1,0,0,0,239,193,1,
        0,0,0,239,197,1,0,0,0,239,200,1,0,0,0,239,203,1,0,0,0,239,207,1,
        0,0,0,239,211,1,0,0,0,239,214,1,0,0,0,239,217,1,0,0,0,239,220,1,
        0,0,0,239,224,1,0,0,0,239,227,1,0,0,0,239,230,1,0,0,0,239,236,1,
        0,0,0,240,243,1,0,0,0,241,239,1,0,0,0,241,242,1,0,0,0,242,25,1,0,
        0,0,243,241,1,0,0,0,244,251,5,60,0,0,245,247,5,2,0,0,246,248,3,32,
        16,0,247,246,1,0,0,0,247,248,1,0,0,0,248,249,1,0,0,0,249,251,5,3,
        0,0,250,244,1,0,0,0,250,245,1,0,0,0,251,27,1,0,0,0,252,253,5,71,
        0,0,253,254,5,1,0,0,254,255,3,24,12,0,255,29,1,0,0,0,256,257,5,14,
        0,0,257,260,5,73,0,0,258,259,5,5,0,0,259,261,5,73,0,0,260,258,1,
        0,0,0,260,261,1,0,0,0,261,262,1,0,0,0,262,263,5,15,0,0,263,31,1,
        0,0,0,264,269,3,24,12,0,265,266,5,5,0,0,266,268,3,24,12,0,267,265,
        1,0,0,0,268,271,1,0,0,0,269,267,1,0,0,0,269,270,1,0,0,0,270,33,1,
        0,0,0,271,269,1,0,0,0,272,273,7,0,0,0,273,274,3,30,15,0,274,35,1,
        0,0,0,275,276,7,1,0,0,276,277,3,30,15,0,277,37,1,0,0,0,278,279,7,
        2,0,0,279,39,1,0,0,0,280,281,7,3,0,0,281,41,1,0,0,0,282,283,7,4,
        0,0,283,43,1,0,0,0,284,285,7,5,0,0,285,45,1,0,0,0,286,287,7,6,0,
        0,287,47,1,0,0,0,288,289,7,7,0,0,289,49,1,0,0,0,21,54,56,63,71,80,
        83,90,104,120,126,137,146,151,170,187,239,241,247,250,260,269
    ]

class C2POParser ( Parser ):

    grammarFileName = "C2PO.g"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ "<INVALID>", "':'", "'{'", "'}'", "';'", "','", "'\\u27E8'", 
                     "'\\u27E9'", "'='", "'=>'", "'('", "')'", "'.'", "'?'", 
                     "'['", "']'", "'STRUCT'", "'INPUT'", "'DEFINE'", "'SPEC'", 
                     "'Order'", "'set'", "<INVALID>", "<INVALID>", "<INVALID>", 
                     "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                     "<INVALID>", "'~'", "'&'", "'|'", "'^'", "'<<'", "'>>'", 
                     "'=='", "<INVALID>", "<INVALID>", "<INVALID>", "'>'", 
                     "'<'", "'+'", "'-'", "<INVALID>", "<INVALID>", "'%'", 
                     "'**'", "'\\u221A'", "<INVALID>", "<INVALID>", "<INVALID>", 
                     "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                     "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                     "'\\u2205'", "'\\u2208'", "'\\u2282'", "'\\u2286'", 
                     "'\\u2211'", "'\\u220F'", "'\\u22C3'", "'\\u22C2'", 
                     "'\\u22C0'", "'\\u22C1'", "'\\u00D7'" ]

    symbolicNames = [ "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "KW_STRUCT", "KW_INPUT", "KW_DEF", "KW_SPEC", "KW_ORDER", 
                      "KW_SET", "LOG_NEG", "LOG_AND", "LOG_OR", "LOG_XOR", 
                      "LOG_IMPL", "LOG_IFF", "TRUE", "FALSE", "BW_NEG", 
                      "BW_AND", "BW_OR", "BW_XOR", "BW_SHIFT_LEFT", "BW_SHIFT_RIGHT", 
                      "REL_EQ", "REL_NEQ", "REL_GTE", "REL_LTE", "REL_GT", 
                      "REL_LT", "ARITH_ADD", "ARITH_SUB", "ARITH_MUL", "ARITH_DIV", 
                      "ARITH_MOD", "ARITH_POW", "ARITH_SQRT", "ARITH_PM", 
                      "TL_GLOBAL", "TL_FUTURE", "TL_NEXT", "TL_SINCE", "TL_ONCE", 
                      "TL_UNTIL", "TL_RELEASE", "TL_HISTORICAL", "FO_FORALL", 
                      "FO_EXISTS", "SW_EMPTY_SET", "SW_MEMBER", "SW_SUBSET", 
                      "SW_SUBSETEQ", "SW_SUM", "SW_PROD", "SW_UNION", "SW_INTERSECTION", 
                      "SW_AND", "SW_OR", "SW_CTPROD", "IDENTIFIER", "FLOAT", 
                      "INT", "COMMENT", "WS" ]

    RULE_start = 0
    RULE_struct_block = 1
    RULE_struct = 2
    RULE_input_block = 3
    RULE_var_list = 4
    RULE_order_list = 5
    RULE_type = 6
    RULE_def_block = 7
    RULE_def = 8
    RULE_spec_block = 9
    RULE_spec = 10
    RULE_contract = 11
    RULE_expr = 12
    RULE_set_expr = 13
    RULE_set_agg_binder = 14
    RULE_interval = 15
    RULE_expr_list = 16
    RULE_tl_unary_op = 17
    RULE_tl_bin_op = 18
    RULE_literal = 19
    RULE_rel_eq_op = 20
    RULE_rel_ineq_op = 21
    RULE_arith_add_op = 22
    RULE_arith_mul_op = 23
    RULE_unary_op = 24

    ruleNames =  [ "start", "struct_block", "struct", "input_block", "var_list", 
                   "order_list", "type", "def_block", "def", "spec_block", 
                   "spec", "contract", "expr", "set_expr", "set_agg_binder", 
                   "interval", "expr_list", "tl_unary_op", "tl_bin_op", 
                   "literal", "rel_eq_op", "rel_ineq_op", "arith_add_op", 
                   "arith_mul_op", "unary_op" ]

    EOF = Token.EOF
    T__0=1
    T__1=2
    T__2=3
    T__3=4
    T__4=5
    T__5=6
    T__6=7
    T__7=8
    T__8=9
    T__9=10
    T__10=11
    T__11=12
    T__12=13
    T__13=14
    T__14=15
    KW_STRUCT=16
    KW_INPUT=17
    KW_DEF=18
    KW_SPEC=19
    KW_ORDER=20
    KW_SET=21
    LOG_NEG=22
    LOG_AND=23
    LOG_OR=24
    LOG_XOR=25
    LOG_IMPL=26
    LOG_IFF=27
    TRUE=28
    FALSE=29
    BW_NEG=30
    BW_AND=31
    BW_OR=32
    BW_XOR=33
    BW_SHIFT_LEFT=34
    BW_SHIFT_RIGHT=35
    REL_EQ=36
    REL_NEQ=37
    REL_GTE=38
    REL_LTE=39
    REL_GT=40
    REL_LT=41
    ARITH_ADD=42
    ARITH_SUB=43
    ARITH_MUL=44
    ARITH_DIV=45
    ARITH_MOD=46
    ARITH_POW=47
    ARITH_SQRT=48
    ARITH_PM=49
    TL_GLOBAL=50
    TL_FUTURE=51
    TL_NEXT=52
    TL_SINCE=53
    TL_ONCE=54
    TL_UNTIL=55
    TL_RELEASE=56
    TL_HISTORICAL=57
    FO_FORALL=58
    FO_EXISTS=59
    SW_EMPTY_SET=60
    SW_MEMBER=61
    SW_SUBSET=62
    SW_SUBSETEQ=63
    SW_SUM=64
    SW_PROD=65
    SW_UNION=66
    SW_INTERSECTION=67
    SW_AND=68
    SW_OR=69
    SW_CTPROD=70
    IDENTIFIER=71
    FLOAT=72
    INT=73
    COMMENT=74
    WS=75

    def __init__(self, input:TokenStream, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.11.1")
        self._interp = ParserATNSimulator(self, self.atn, self.decisionsToDFA, self.sharedContextCache)
        self._predicates = None




    class StartContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def struct_block(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(C2POParser.Struct_blockContext)
            else:
                return self.getTypedRuleContext(C2POParser.Struct_blockContext,i)


        def input_block(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(C2POParser.Input_blockContext)
            else:
                return self.getTypedRuleContext(C2POParser.Input_blockContext,i)


        def def_block(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(C2POParser.Def_blockContext)
            else:
                return self.getTypedRuleContext(C2POParser.Def_blockContext,i)


        def spec_block(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(C2POParser.Spec_blockContext)
            else:
                return self.getTypedRuleContext(C2POParser.Spec_blockContext,i)


        def getRuleIndex(self):
            return C2POParser.RULE_start

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitStart" ):
                return visitor.visitStart(self)
            else:
                return visitor.visitChildren(self)




    def start(self):

        localctx = C2POParser.StartContext(self, self._ctx, self.state)
        self.enterRule(localctx, 0, self.RULE_start)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 56
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while ((_la) & ~0x3f) == 0 and ((1 << _la) & 983040) != 0:
                self.state = 54
                self._errHandler.sync(self)
                token = self._input.LA(1)
                if token in [16]:
                    self.state = 50
                    self.struct_block()
                    pass
                elif token in [17]:
                    self.state = 51
                    self.input_block()
                    pass
                elif token in [18]:
                    self.state = 52
                    self.def_block()
                    pass
                elif token in [19]:
                    self.state = 53
                    self.spec_block()
                    pass
                else:
                    raise NoViableAltException(self)

                self.state = 58
                self._errHandler.sync(self)
                _la = self._input.LA(1)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Struct_blockContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def KW_STRUCT(self):
            return self.getToken(C2POParser.KW_STRUCT, 0)

        def struct(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(C2POParser.StructContext)
            else:
                return self.getTypedRuleContext(C2POParser.StructContext,i)


        def getRuleIndex(self):
            return C2POParser.RULE_struct_block

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitStruct_block" ):
                return visitor.visitStruct_block(self)
            else:
                return visitor.visitChildren(self)




    def struct_block(self):

        localctx = C2POParser.Struct_blockContext(self, self._ctx, self.state)
        self.enterRule(localctx, 2, self.RULE_struct_block)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 59
            self.match(C2POParser.KW_STRUCT)
            self.state = 61 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 60
                self.struct()
                self.state = 63 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (_la==71):
                    break

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class StructContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def IDENTIFIER(self):
            return self.getToken(C2POParser.IDENTIFIER, 0)

        def var_list(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(C2POParser.Var_listContext)
            else:
                return self.getTypedRuleContext(C2POParser.Var_listContext,i)


        def getRuleIndex(self):
            return C2POParser.RULE_struct

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitStruct" ):
                return visitor.visitStruct(self)
            else:
                return visitor.visitChildren(self)




    def struct(self):

        localctx = C2POParser.StructContext(self, self._ctx, self.state)
        self.enterRule(localctx, 4, self.RULE_struct)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 65
            self.match(C2POParser.IDENTIFIER)
            self.state = 66
            self.match(C2POParser.T__0)
            self.state = 67
            self.match(C2POParser.T__1)
            self.state = 69 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 68
                self.var_list()
                self.state = 71 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (_la==71):
                    break

            self.state = 73
            self.match(C2POParser.T__2)
            self.state = 74
            self.match(C2POParser.T__3)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Input_blockContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def KW_INPUT(self):
            return self.getToken(C2POParser.KW_INPUT, 0)

        def var_list(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(C2POParser.Var_listContext)
            else:
                return self.getTypedRuleContext(C2POParser.Var_listContext,i)


        def order_list(self):
            return self.getTypedRuleContext(C2POParser.Order_listContext,0)


        def getRuleIndex(self):
            return C2POParser.RULE_input_block

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitInput_block" ):
                return visitor.visitInput_block(self)
            else:
                return visitor.visitChildren(self)




    def input_block(self):

        localctx = C2POParser.Input_blockContext(self, self._ctx, self.state)
        self.enterRule(localctx, 6, self.RULE_input_block)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 76
            self.match(C2POParser.KW_INPUT)
            self.state = 78 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 77
                self.var_list()
                self.state = 80 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (_la==71):
                    break

            self.state = 83
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==20:
                self.state = 82
                self.order_list()


        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Var_listContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def IDENTIFIER(self, i:int=None):
            if i is None:
                return self.getTokens(C2POParser.IDENTIFIER)
            else:
                return self.getToken(C2POParser.IDENTIFIER, i)

        def type_(self):
            return self.getTypedRuleContext(C2POParser.TypeContext,0)


        def getRuleIndex(self):
            return C2POParser.RULE_var_list

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitVar_list" ):
                return visitor.visitVar_list(self)
            else:
                return visitor.visitChildren(self)




    def var_list(self):

        localctx = C2POParser.Var_listContext(self, self._ctx, self.state)
        self.enterRule(localctx, 8, self.RULE_var_list)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 85
            self.match(C2POParser.IDENTIFIER)
            self.state = 90
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==5:
                self.state = 86
                self.match(C2POParser.T__4)
                self.state = 87
                self.match(C2POParser.IDENTIFIER)
                self.state = 92
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 93
            self.match(C2POParser.T__0)
            self.state = 94
            self.type_()
            self.state = 95
            self.match(C2POParser.T__3)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Order_listContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def KW_ORDER(self):
            return self.getToken(C2POParser.KW_ORDER, 0)

        def IDENTIFIER(self, i:int=None):
            if i is None:
                return self.getTokens(C2POParser.IDENTIFIER)
            else:
                return self.getToken(C2POParser.IDENTIFIER, i)

        def getRuleIndex(self):
            return C2POParser.RULE_order_list

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitOrder_list" ):
                return visitor.visitOrder_list(self)
            else:
                return visitor.visitChildren(self)




    def order_list(self):

        localctx = C2POParser.Order_listContext(self, self._ctx, self.state)
        self.enterRule(localctx, 10, self.RULE_order_list)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 97
            self.match(C2POParser.KW_ORDER)
            self.state = 98
            self.match(C2POParser.T__0)
            self.state = 99
            self.match(C2POParser.IDENTIFIER)
            self.state = 104
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==5:
                self.state = 100
                self.match(C2POParser.T__4)
                self.state = 101
                self.match(C2POParser.IDENTIFIER)
                self.state = 106
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 107
            self.match(C2POParser.T__3)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class TypeContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def IDENTIFIER(self):
            return self.getToken(C2POParser.IDENTIFIER, 0)

        def KW_SET(self):
            return self.getToken(C2POParser.KW_SET, 0)

        def type_(self):
            return self.getTypedRuleContext(C2POParser.TypeContext,0)


        def REL_LT(self):
            return self.getToken(C2POParser.REL_LT, 0)

        def REL_GT(self):
            return self.getToken(C2POParser.REL_GT, 0)

        def getRuleIndex(self):
            return C2POParser.RULE_type

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitType" ):
                return visitor.visitType(self)
            else:
                return visitor.visitChildren(self)




    def type_(self):

        localctx = C2POParser.TypeContext(self, self._ctx, self.state)
        self.enterRule(localctx, 12, self.RULE_type)
        try:
            self.state = 120
            self._errHandler.sync(self)
            la_ = self._interp.adaptivePredict(self._input,8,self._ctx)
            if la_ == 1:
                self.enterOuterAlt(localctx, 1)
                self.state = 109
                self.match(C2POParser.IDENTIFIER)
                pass

            elif la_ == 2:
                self.enterOuterAlt(localctx, 2)
                self.state = 110
                self.match(C2POParser.KW_SET)
                self.state = 111
                self.match(C2POParser.T__5)
                self.state = 112
                self.type_()
                self.state = 113
                self.match(C2POParser.T__6)
                pass

            elif la_ == 3:
                self.enterOuterAlt(localctx, 3)
                self.state = 115
                self.match(C2POParser.KW_SET)
                self.state = 116
                self.match(C2POParser.REL_LT)
                self.state = 117
                self.type_()
                self.state = 118
                self.match(C2POParser.REL_GT)
                pass


        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Def_blockContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def KW_DEF(self):
            return self.getToken(C2POParser.KW_DEF, 0)

        def def_(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(C2POParser.DefContext)
            else:
                return self.getTypedRuleContext(C2POParser.DefContext,i)


        def getRuleIndex(self):
            return C2POParser.RULE_def_block

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitDef_block" ):
                return visitor.visitDef_block(self)
            else:
                return visitor.visitChildren(self)




    def def_block(self):

        localctx = C2POParser.Def_blockContext(self, self._ctx, self.state)
        self.enterRule(localctx, 14, self.RULE_def_block)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 122
            self.match(C2POParser.KW_DEF)
            self.state = 124 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 123
                self.def_()
                self.state = 126 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (_la==71):
                    break

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class DefContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def IDENTIFIER(self):
            return self.getToken(C2POParser.IDENTIFIER, 0)

        def expr(self):
            return self.getTypedRuleContext(C2POParser.ExprContext,0)


        def getRuleIndex(self):
            return C2POParser.RULE_def

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitDef" ):
                return visitor.visitDef(self)
            else:
                return visitor.visitChildren(self)




    def def_(self):

        localctx = C2POParser.DefContext(self, self._ctx, self.state)
        self.enterRule(localctx, 16, self.RULE_def)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 128
            self.match(C2POParser.IDENTIFIER)
            self.state = 129
            self.match(C2POParser.T__7)
            self.state = 130
            self.expr(0)
            self.state = 131
            self.match(C2POParser.T__3)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Spec_blockContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def KW_SPEC(self):
            return self.getToken(C2POParser.KW_SPEC, 0)

        def spec(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(C2POParser.SpecContext)
            else:
                return self.getTypedRuleContext(C2POParser.SpecContext,i)


        def getRuleIndex(self):
            return C2POParser.RULE_spec_block

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitSpec_block" ):
                return visitor.visitSpec_block(self)
            else:
                return visitor.visitChildren(self)




    def spec_block(self):

        localctx = C2POParser.Spec_blockContext(self, self._ctx, self.state)
        self.enterRule(localctx, 18, self.RULE_spec_block)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 133
            self.match(C2POParser.KW_SPEC)
            self.state = 135 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 134
                self.spec()
                self.state = 137 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (((_la) & ~0x3f) == 0 and ((1 << _la) & 1318441986931295236) != 0 or (((_la - 71)) & ~0x3f) == 0 and ((1 << (_la - 71)) & 7) != 0):
                    break

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class SpecContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def IDENTIFIER(self):
            return self.getToken(C2POParser.IDENTIFIER, 0)

        def contract(self):
            return self.getTypedRuleContext(C2POParser.ContractContext,0)


        def expr(self):
            return self.getTypedRuleContext(C2POParser.ExprContext,0)


        def getRuleIndex(self):
            return C2POParser.RULE_spec

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitSpec" ):
                return visitor.visitSpec(self)
            else:
                return visitor.visitChildren(self)




    def spec(self):

        localctx = C2POParser.SpecContext(self, self._ctx, self.state)
        self.enterRule(localctx, 20, self.RULE_spec)
        try:
            self.state = 151
            self._errHandler.sync(self)
            la_ = self._interp.adaptivePredict(self._input,12,self._ctx)
            if la_ == 1:
                self.enterOuterAlt(localctx, 1)
                self.state = 139
                self.match(C2POParser.IDENTIFIER)
                self.state = 140
                self.match(C2POParser.T__0)
                self.state = 141
                self.contract()
                self.state = 142
                self.match(C2POParser.T__3)
                pass

            elif la_ == 2:
                self.enterOuterAlt(localctx, 2)
                self.state = 146
                self._errHandler.sync(self)
                la_ = self._interp.adaptivePredict(self._input,11,self._ctx)
                if la_ == 1:
                    self.state = 144
                    self.match(C2POParser.IDENTIFIER)
                    self.state = 145
                    self.match(C2POParser.T__0)


                self.state = 148
                self.expr(0)
                self.state = 149
                self.match(C2POParser.T__3)
                pass


        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class ContractContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(C2POParser.ExprContext)
            else:
                return self.getTypedRuleContext(C2POParser.ExprContext,i)


        def getRuleIndex(self):
            return C2POParser.RULE_contract

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitContract" ):
                return visitor.visitContract(self)
            else:
                return visitor.visitChildren(self)




    def contract(self):

        localctx = C2POParser.ContractContext(self, self._ctx, self.state)
        self.enterRule(localctx, 22, self.RULE_contract)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 153
            self.expr(0)
            self.state = 154
            self.match(C2POParser.T__8)
            self.state = 155
            self.expr(0)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class ExprContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser


        def getRuleIndex(self):
            return C2POParser.RULE_expr

     
        def copyFrom(self, ctx:ParserRuleContext):
            super().copyFrom(ctx)


    class ArithAddExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a C2POParser.ExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(C2POParser.ExprContext)
            else:
                return self.getTypedRuleContext(C2POParser.ExprContext,i)

        def arith_add_op(self):
            return self.getTypedRuleContext(C2POParser.Arith_add_opContext,0)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitArithAddExpr" ):
                return visitor.visitArithAddExpr(self)
            else:
                return visitor.visitChildren(self)


    class BWExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a C2POParser.ExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(C2POParser.ExprContext)
            else:
                return self.getTypedRuleContext(C2POParser.ExprContext,i)

        def BW_SHIFT_LEFT(self):
            return self.getToken(C2POParser.BW_SHIFT_LEFT, 0)
        def BW_SHIFT_RIGHT(self):
            return self.getToken(C2POParser.BW_SHIFT_RIGHT, 0)
        def BW_AND(self):
            return self.getToken(C2POParser.BW_AND, 0)
        def BW_XOR(self):
            return self.getToken(C2POParser.BW_XOR, 0)
        def BW_OR(self):
            return self.getToken(C2POParser.BW_OR, 0)

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitBWExpr" ):
                return visitor.visitBWExpr(self)
            else:
                return visitor.visitChildren(self)


    class TLBinExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a C2POParser.ExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(C2POParser.ExprContext)
            else:
                return self.getTypedRuleContext(C2POParser.ExprContext,i)

        def tl_bin_op(self):
            return self.getTypedRuleContext(C2POParser.Tl_bin_opContext,0)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitTLBinExpr" ):
                return visitor.visitTLBinExpr(self)
            else:
                return visitor.visitChildren(self)


    class ArithMulExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a C2POParser.ExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(C2POParser.ExprContext)
            else:
                return self.getTypedRuleContext(C2POParser.ExprContext,i)

        def arith_mul_op(self):
            return self.getTypedRuleContext(C2POParser.Arith_mul_opContext,0)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitArithMulExpr" ):
                return visitor.visitArithMulExpr(self)
            else:
                return visitor.visitChildren(self)


    class RelExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a C2POParser.ExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(C2POParser.ExprContext)
            else:
                return self.getTypedRuleContext(C2POParser.ExprContext,i)

        def rel_ineq_op(self):
            return self.getTypedRuleContext(C2POParser.Rel_ineq_opContext,0)

        def rel_eq_op(self):
            return self.getTypedRuleContext(C2POParser.Rel_eq_opContext,0)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitRelExpr" ):
                return visitor.visitRelExpr(self)
            else:
                return visitor.visitChildren(self)


    class SetAggExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a C2POParser.ExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def IDENTIFIER(self):
            return self.getToken(C2POParser.IDENTIFIER, 0)
        def set_agg_binder(self):
            return self.getTypedRuleContext(C2POParser.Set_agg_binderContext,0)

        def expr(self):
            return self.getTypedRuleContext(C2POParser.ExprContext,0)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitSetAggExpr" ):
                return visitor.visitSetAggExpr(self)
            else:
                return visitor.visitChildren(self)


    class FuncExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a C2POParser.ExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def IDENTIFIER(self):
            return self.getToken(C2POParser.IDENTIFIER, 0)
        def expr_list(self):
            return self.getTypedRuleContext(C2POParser.Expr_listContext,0)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitFuncExpr" ):
                return visitor.visitFuncExpr(self)
            else:
                return visitor.visitChildren(self)


    class UnaryExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a C2POParser.ExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def ARITH_SUB(self):
            return self.getToken(C2POParser.ARITH_SUB, 0)
        def expr(self):
            return self.getTypedRuleContext(C2POParser.ExprContext,0)

        def ARITH_ADD(self):
            return self.getToken(C2POParser.ARITH_ADD, 0)
        def BW_NEG(self):
            return self.getToken(C2POParser.BW_NEG, 0)

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitUnaryExpr" ):
                return visitor.visitUnaryExpr(self)
            else:
                return visitor.visitChildren(self)


    class TLUnaryExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a C2POParser.ExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def tl_unary_op(self):
            return self.getTypedRuleContext(C2POParser.Tl_unary_opContext,0)

        def expr(self):
            return self.getTypedRuleContext(C2POParser.ExprContext,0)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitTLUnaryExpr" ):
                return visitor.visitTLUnaryExpr(self)
            else:
                return visitor.visitChildren(self)


    class StructMemberExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a C2POParser.ExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def expr(self):
            return self.getTypedRuleContext(C2POParser.ExprContext,0)

        def IDENTIFIER(self):
            return self.getToken(C2POParser.IDENTIFIER, 0)

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitStructMemberExpr" ):
                return visitor.visitStructMemberExpr(self)
            else:
                return visitor.visitChildren(self)


    class LogBinExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a C2POParser.ExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(C2POParser.ExprContext)
            else:
                return self.getTypedRuleContext(C2POParser.ExprContext,i)

        def LOG_AND(self):
            return self.getToken(C2POParser.LOG_AND, 0)
        def LOG_OR(self):
            return self.getToken(C2POParser.LOG_OR, 0)

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitLogBinExpr" ):
                return visitor.visitLogBinExpr(self)
            else:
                return visitor.visitChildren(self)


    class SetExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a C2POParser.ExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def set_expr(self):
            return self.getTypedRuleContext(C2POParser.Set_exprContext,0)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitSetExpr" ):
                return visitor.visitSetExpr(self)
            else:
                return visitor.visitChildren(self)


    class ParensExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a C2POParser.ExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def expr(self):
            return self.getTypedRuleContext(C2POParser.ExprContext,0)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitParensExpr" ):
                return visitor.visitParensExpr(self)
            else:
                return visitor.visitChildren(self)


    class LiteralExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a C2POParser.ExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def literal(self):
            return self.getTypedRuleContext(C2POParser.LiteralContext,0)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitLiteralExpr" ):
                return visitor.visitLiteralExpr(self)
            else:
                return visitor.visitChildren(self)


    class TernaryExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a C2POParser.ExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(C2POParser.ExprContext)
            else:
                return self.getTypedRuleContext(C2POParser.ExprContext,i)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitTernaryExpr" ):
                return visitor.visitTernaryExpr(self)
            else:
                return visitor.visitChildren(self)



    def expr(self, _p:int=0):
        _parentctx = self._ctx
        _parentState = self.state
        localctx = C2POParser.ExprContext(self, self._ctx, _parentState)
        _prevctx = localctx
        _startState = 24
        self.enterRecursionRule(localctx, 24, self.RULE_expr, _p)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 187
            self._errHandler.sync(self)
            la_ = self._interp.adaptivePredict(self._input,14,self._ctx)
            if la_ == 1:
                localctx = C2POParser.SetExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx

                self.state = 158
                self.set_expr()
                pass

            elif la_ == 2:
                localctx = C2POParser.SetAggExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 159
                self.match(C2POParser.IDENTIFIER)
                self.state = 160
                self.match(C2POParser.T__9)
                self.state = 161
                self.set_agg_binder()
                self.state = 162
                self.match(C2POParser.T__10)
                self.state = 163
                self.match(C2POParser.T__9)
                self.state = 164
                self.expr(0)
                self.state = 165
                self.match(C2POParser.T__10)
                pass

            elif la_ == 3:
                localctx = C2POParser.FuncExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 167
                self.match(C2POParser.IDENTIFIER)
                self.state = 168
                self.match(C2POParser.T__9)
                self.state = 170
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if ((_la) & ~0x3f) == 0 and ((1 << _la) & 1318441986931295236) != 0 or (((_la - 71)) & ~0x3f) == 0 and ((1 << (_la - 71)) & 7) != 0:
                    self.state = 169
                    self.expr_list()


                self.state = 172
                self.match(C2POParser.T__10)
                pass

            elif la_ == 4:
                localctx = C2POParser.UnaryExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 173
                self.match(C2POParser.ARITH_SUB)
                self.state = 174
                self.expr(19)
                pass

            elif la_ == 5:
                localctx = C2POParser.UnaryExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 175
                self.match(C2POParser.ARITH_ADD)
                self.state = 176
                self.expr(18)
                pass

            elif la_ == 6:
                localctx = C2POParser.UnaryExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 177
                self.match(C2POParser.BW_NEG)
                self.state = 178
                self.expr(17)
                pass

            elif la_ == 7:
                localctx = C2POParser.TLUnaryExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 179
                self.tl_unary_op()
                self.state = 180
                self.expr(6)
                pass

            elif la_ == 8:
                localctx = C2POParser.ParensExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 182
                self.match(C2POParser.T__9)
                self.state = 183
                self.expr(0)
                self.state = 184
                self.match(C2POParser.T__10)
                pass

            elif la_ == 9:
                localctx = C2POParser.LiteralExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 186
                self.literal()
                pass


            self._ctx.stop = self._input.LT(-1)
            self.state = 241
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,16,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    if self._parseListeners is not None:
                        self.triggerExitRuleEvent()
                    _prevctx = localctx
                    self.state = 239
                    self._errHandler.sync(self)
                    la_ = self._interp.adaptivePredict(self._input,15,self._ctx)
                    if la_ == 1:
                        localctx = C2POParser.ArithMulExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 189
                        if not self.precpred(self._ctx, 16):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 16)")
                        self.state = 190
                        self.arith_mul_op()
                        self.state = 191
                        self.expr(17)
                        pass

                    elif la_ == 2:
                        localctx = C2POParser.ArithAddExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 193
                        if not self.precpred(self._ctx, 15):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 15)")
                        self.state = 194
                        self.arith_add_op()
                        self.state = 195
                        self.expr(16)
                        pass

                    elif la_ == 3:
                        localctx = C2POParser.BWExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 197
                        if not self.precpred(self._ctx, 14):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 14)")
                        self.state = 198
                        self.match(C2POParser.BW_SHIFT_LEFT)
                        self.state = 199
                        self.expr(15)
                        pass

                    elif la_ == 4:
                        localctx = C2POParser.BWExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 200
                        if not self.precpred(self._ctx, 13):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 13)")
                        self.state = 201
                        self.match(C2POParser.BW_SHIFT_RIGHT)
                        self.state = 202
                        self.expr(14)
                        pass

                    elif la_ == 5:
                        localctx = C2POParser.RelExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 203
                        if not self.precpred(self._ctx, 12):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 12)")
                        self.state = 204
                        self.rel_ineq_op()
                        self.state = 205
                        self.expr(13)
                        pass

                    elif la_ == 6:
                        localctx = C2POParser.RelExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 207
                        if not self.precpred(self._ctx, 11):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 11)")
                        self.state = 208
                        self.rel_eq_op()
                        self.state = 209
                        self.expr(12)
                        pass

                    elif la_ == 7:
                        localctx = C2POParser.BWExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 211
                        if not self.precpred(self._ctx, 10):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 10)")
                        self.state = 212
                        self.match(C2POParser.BW_AND)
                        self.state = 213
                        self.expr(11)
                        pass

                    elif la_ == 8:
                        localctx = C2POParser.BWExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 214
                        if not self.precpred(self._ctx, 9):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 9)")
                        self.state = 215
                        self.match(C2POParser.BW_XOR)
                        self.state = 216
                        self.expr(10)
                        pass

                    elif la_ == 9:
                        localctx = C2POParser.BWExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 217
                        if not self.precpred(self._ctx, 8):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 8)")
                        self.state = 218
                        self.match(C2POParser.BW_OR)
                        self.state = 219
                        self.expr(9)
                        pass

                    elif la_ == 10:
                        localctx = C2POParser.TLBinExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 220
                        if not self.precpred(self._ctx, 7):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 7)")
                        self.state = 221
                        self.tl_bin_op()
                        self.state = 222
                        self.expr(8)
                        pass

                    elif la_ == 11:
                        localctx = C2POParser.LogBinExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 224
                        if not self.precpred(self._ctx, 5):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 5)")
                        self.state = 225
                        self.match(C2POParser.LOG_AND)
                        self.state = 226
                        self.expr(6)
                        pass

                    elif la_ == 12:
                        localctx = C2POParser.LogBinExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 227
                        if not self.precpred(self._ctx, 4):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 4)")
                        self.state = 228
                        self.match(C2POParser.LOG_OR)
                        self.state = 229
                        self.expr(5)
                        pass

                    elif la_ == 13:
                        localctx = C2POParser.TernaryExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 230
                        if not self.precpred(self._ctx, 3):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 3)")
                        self.state = 231
                        self.match(C2POParser.T__12)
                        self.state = 232
                        self.expr(0)
                        self.state = 233
                        self.match(C2POParser.T__0)
                        self.state = 234
                        self.expr(4)
                        pass

                    elif la_ == 14:
                        localctx = C2POParser.StructMemberExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 236
                        if not self.precpred(self._ctx, 20):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 20)")
                        self.state = 237
                        self.match(C2POParser.T__11)
                        self.state = 238
                        self.match(C2POParser.IDENTIFIER)
                        pass

             
                self.state = 243
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,16,self._ctx)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.unrollRecursionContexts(_parentctx)
        return localctx


    class Set_exprContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def SW_EMPTY_SET(self):
            return self.getToken(C2POParser.SW_EMPTY_SET, 0)

        def expr_list(self):
            return self.getTypedRuleContext(C2POParser.Expr_listContext,0)


        def getRuleIndex(self):
            return C2POParser.RULE_set_expr

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitSet_expr" ):
                return visitor.visitSet_expr(self)
            else:
                return visitor.visitChildren(self)




    def set_expr(self):

        localctx = C2POParser.Set_exprContext(self, self._ctx, self.state)
        self.enterRule(localctx, 26, self.RULE_set_expr)
        self._la = 0 # Token type
        try:
            self.state = 250
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [60]:
                self.enterOuterAlt(localctx, 1)
                self.state = 244
                self.match(C2POParser.SW_EMPTY_SET)
                pass
            elif token in [2]:
                self.enterOuterAlt(localctx, 2)
                self.state = 245
                self.match(C2POParser.T__1)
                self.state = 247
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if ((_la) & ~0x3f) == 0 and ((1 << _la) & 1318441986931295236) != 0 or (((_la - 71)) & ~0x3f) == 0 and ((1 << (_la - 71)) & 7) != 0:
                    self.state = 246
                    self.expr_list()


                self.state = 249
                self.match(C2POParser.T__2)
                pass
            else:
                raise NoViableAltException(self)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Set_agg_binderContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def IDENTIFIER(self):
            return self.getToken(C2POParser.IDENTIFIER, 0)

        def expr(self):
            return self.getTypedRuleContext(C2POParser.ExprContext,0)


        def getRuleIndex(self):
            return C2POParser.RULE_set_agg_binder

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitSet_agg_binder" ):
                return visitor.visitSet_agg_binder(self)
            else:
                return visitor.visitChildren(self)




    def set_agg_binder(self):

        localctx = C2POParser.Set_agg_binderContext(self, self._ctx, self.state)
        self.enterRule(localctx, 28, self.RULE_set_agg_binder)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 252
            self.match(C2POParser.IDENTIFIER)
            self.state = 253
            self.match(C2POParser.T__0)
            self.state = 254
            self.expr(0)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class IntervalContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def INT(self, i:int=None):
            if i is None:
                return self.getTokens(C2POParser.INT)
            else:
                return self.getToken(C2POParser.INT, i)

        def getRuleIndex(self):
            return C2POParser.RULE_interval

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitInterval" ):
                return visitor.visitInterval(self)
            else:
                return visitor.visitChildren(self)




    def interval(self):

        localctx = C2POParser.IntervalContext(self, self._ctx, self.state)
        self.enterRule(localctx, 30, self.RULE_interval)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 256
            self.match(C2POParser.T__13)
            self.state = 257
            self.match(C2POParser.INT)
            self.state = 260
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==5:
                self.state = 258
                self.match(C2POParser.T__4)
                self.state = 259
                self.match(C2POParser.INT)


            self.state = 262
            self.match(C2POParser.T__14)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Expr_listContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(C2POParser.ExprContext)
            else:
                return self.getTypedRuleContext(C2POParser.ExprContext,i)


        def getRuleIndex(self):
            return C2POParser.RULE_expr_list

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitExpr_list" ):
                return visitor.visitExpr_list(self)
            else:
                return visitor.visitChildren(self)




    def expr_list(self):

        localctx = C2POParser.Expr_listContext(self, self._ctx, self.state)
        self.enterRule(localctx, 32, self.RULE_expr_list)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 264
            self.expr(0)
            self.state = 269
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==5:
                self.state = 265
                self.match(C2POParser.T__4)
                self.state = 266
                self.expr(0)
                self.state = 271
                self._errHandler.sync(self)
                _la = self._input.LA(1)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Tl_unary_opContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def interval(self):
            return self.getTypedRuleContext(C2POParser.IntervalContext,0)


        def TL_GLOBAL(self):
            return self.getToken(C2POParser.TL_GLOBAL, 0)

        def TL_FUTURE(self):
            return self.getToken(C2POParser.TL_FUTURE, 0)

        def TL_HISTORICAL(self):
            return self.getToken(C2POParser.TL_HISTORICAL, 0)

        def TL_ONCE(self):
            return self.getToken(C2POParser.TL_ONCE, 0)

        def getRuleIndex(self):
            return C2POParser.RULE_tl_unary_op

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitTl_unary_op" ):
                return visitor.visitTl_unary_op(self)
            else:
                return visitor.visitChildren(self)




    def tl_unary_op(self):

        localctx = C2POParser.Tl_unary_opContext(self, self._ctx, self.state)
        self.enterRule(localctx, 34, self.RULE_tl_unary_op)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 272
            _la = self._input.LA(1)
            if not(((_la) & ~0x3f) == 0 and ((1 << _la) & 165507286305865728) != 0):
                self._errHandler.recoverInline(self)
            else:
                self._errHandler.reportMatch(self)
                self.consume()
            self.state = 273
            self.interval()
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Tl_bin_opContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def interval(self):
            return self.getTypedRuleContext(C2POParser.IntervalContext,0)


        def TL_UNTIL(self):
            return self.getToken(C2POParser.TL_UNTIL, 0)

        def TL_RELEASE(self):
            return self.getToken(C2POParser.TL_RELEASE, 0)

        def TL_SINCE(self):
            return self.getToken(C2POParser.TL_SINCE, 0)

        def getRuleIndex(self):
            return C2POParser.RULE_tl_bin_op

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitTl_bin_op" ):
                return visitor.visitTl_bin_op(self)
            else:
                return visitor.visitChildren(self)




    def tl_bin_op(self):

        localctx = C2POParser.Tl_bin_opContext(self, self._ctx, self.state)
        self.enterRule(localctx, 36, self.RULE_tl_bin_op)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 275
            _la = self._input.LA(1)
            if not(((_la) & ~0x3f) == 0 and ((1 << _la) & 117093590311632896) != 0):
                self._errHandler.recoverInline(self)
            else:
                self._errHandler.reportMatch(self)
                self.consume()
            self.state = 276
            self.interval()
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class LiteralContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def IDENTIFIER(self):
            return self.getToken(C2POParser.IDENTIFIER, 0)

        def TRUE(self):
            return self.getToken(C2POParser.TRUE, 0)

        def FALSE(self):
            return self.getToken(C2POParser.FALSE, 0)

        def INT(self):
            return self.getToken(C2POParser.INT, 0)

        def FLOAT(self):
            return self.getToken(C2POParser.FLOAT, 0)

        def getRuleIndex(self):
            return C2POParser.RULE_literal

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitLiteral" ):
                return visitor.visitLiteral(self)
            else:
                return visitor.visitChildren(self)




    def literal(self):

        localctx = C2POParser.LiteralContext(self, self._ctx, self.state)
        self.enterRule(localctx, 38, self.RULE_literal)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 278
            _la = self._input.LA(1)
            if not((((_la - 28)) & ~0x3f) == 0 and ((1 << (_la - 28)) & 61572651155459) != 0):
                self._errHandler.recoverInline(self)
            else:
                self._errHandler.reportMatch(self)
                self.consume()
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Rel_eq_opContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def REL_EQ(self):
            return self.getToken(C2POParser.REL_EQ, 0)

        def REL_NEQ(self):
            return self.getToken(C2POParser.REL_NEQ, 0)

        def getRuleIndex(self):
            return C2POParser.RULE_rel_eq_op

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitRel_eq_op" ):
                return visitor.visitRel_eq_op(self)
            else:
                return visitor.visitChildren(self)




    def rel_eq_op(self):

        localctx = C2POParser.Rel_eq_opContext(self, self._ctx, self.state)
        self.enterRule(localctx, 40, self.RULE_rel_eq_op)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 280
            _la = self._input.LA(1)
            if not(_la==36 or _la==37):
                self._errHandler.recoverInline(self)
            else:
                self._errHandler.reportMatch(self)
                self.consume()
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Rel_ineq_opContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def REL_GT(self):
            return self.getToken(C2POParser.REL_GT, 0)

        def REL_LT(self):
            return self.getToken(C2POParser.REL_LT, 0)

        def REL_GTE(self):
            return self.getToken(C2POParser.REL_GTE, 0)

        def REL_LTE(self):
            return self.getToken(C2POParser.REL_LTE, 0)

        def getRuleIndex(self):
            return C2POParser.RULE_rel_ineq_op

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitRel_ineq_op" ):
                return visitor.visitRel_ineq_op(self)
            else:
                return visitor.visitChildren(self)




    def rel_ineq_op(self):

        localctx = C2POParser.Rel_ineq_opContext(self, self._ctx, self.state)
        self.enterRule(localctx, 42, self.RULE_rel_ineq_op)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 282
            _la = self._input.LA(1)
            if not(((_la) & ~0x3f) == 0 and ((1 << _la) & 4123168604160) != 0):
                self._errHandler.recoverInline(self)
            else:
                self._errHandler.reportMatch(self)
                self.consume()
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Arith_add_opContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def ARITH_ADD(self):
            return self.getToken(C2POParser.ARITH_ADD, 0)

        def ARITH_SUB(self):
            return self.getToken(C2POParser.ARITH_SUB, 0)

        def getRuleIndex(self):
            return C2POParser.RULE_arith_add_op

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitArith_add_op" ):
                return visitor.visitArith_add_op(self)
            else:
                return visitor.visitChildren(self)




    def arith_add_op(self):

        localctx = C2POParser.Arith_add_opContext(self, self._ctx, self.state)
        self.enterRule(localctx, 44, self.RULE_arith_add_op)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 284
            _la = self._input.LA(1)
            if not(_la==42 or _la==43):
                self._errHandler.recoverInline(self)
            else:
                self._errHandler.reportMatch(self)
                self.consume()
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Arith_mul_opContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def ARITH_MUL(self):
            return self.getToken(C2POParser.ARITH_MUL, 0)

        def ARITH_DIV(self):
            return self.getToken(C2POParser.ARITH_DIV, 0)

        def ARITH_MOD(self):
            return self.getToken(C2POParser.ARITH_MOD, 0)

        def getRuleIndex(self):
            return C2POParser.RULE_arith_mul_op

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitArith_mul_op" ):
                return visitor.visitArith_mul_op(self)
            else:
                return visitor.visitChildren(self)




    def arith_mul_op(self):

        localctx = C2POParser.Arith_mul_opContext(self, self._ctx, self.state)
        self.enterRule(localctx, 46, self.RULE_arith_mul_op)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 286
            _la = self._input.LA(1)
            if not(((_la) & ~0x3f) == 0 and ((1 << _la) & 123145302310912) != 0):
                self._errHandler.recoverInline(self)
            else:
                self._errHandler.reportMatch(self)
                self.consume()
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Unary_opContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def ARITH_SUB(self):
            return self.getToken(C2POParser.ARITH_SUB, 0)

        def BW_NEG(self):
            return self.getToken(C2POParser.BW_NEG, 0)

        def getRuleIndex(self):
            return C2POParser.RULE_unary_op

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitUnary_op" ):
                return visitor.visitUnary_op(self)
            else:
                return visitor.visitChildren(self)




    def unary_op(self):

        localctx = C2POParser.Unary_opContext(self, self._ctx, self.state)
        self.enterRule(localctx, 48, self.RULE_unary_op)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 288
            _la = self._input.LA(1)
            if not(_la==30 or _la==43):
                self._errHandler.recoverInline(self)
            else:
                self._errHandler.reportMatch(self)
                self.consume()
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx



    def sempred(self, localctx:RuleContext, ruleIndex:int, predIndex:int):
        if self._predicates == None:
            self._predicates = dict()
        self._predicates[12] = self.expr_sempred
        pred = self._predicates.get(ruleIndex, None)
        if pred is None:
            raise Exception("No predicate with index:" + str(ruleIndex))
        else:
            return pred(localctx, predIndex)

    def expr_sempred(self, localctx:ExprContext, predIndex:int):
            if predIndex == 0:
                return self.precpred(self._ctx, 16)
         

            if predIndex == 1:
                return self.precpred(self._ctx, 15)
         

            if predIndex == 2:
                return self.precpred(self._ctx, 14)
         

            if predIndex == 3:
                return self.precpred(self._ctx, 13)
         

            if predIndex == 4:
                return self.precpred(self._ctx, 12)
         

            if predIndex == 5:
                return self.precpred(self._ctx, 11)
         

            if predIndex == 6:
                return self.precpred(self._ctx, 10)
         

            if predIndex == 7:
                return self.precpred(self._ctx, 9)
         

            if predIndex == 8:
                return self.precpred(self._ctx, 8)
         

            if predIndex == 9:
                return self.precpred(self._ctx, 7)
         

            if predIndex == 10:
                return self.precpred(self._ctx, 5)
         

            if predIndex == 11:
                return self.precpred(self._ctx, 4)
         

            if predIndex == 12:
                return self.precpred(self._ctx, 3)
         

            if predIndex == 13:
                return self.precpred(self._ctx, 20)
         




