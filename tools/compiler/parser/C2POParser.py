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
        4,1,75,290,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,2,6,7,
        6,2,7,7,7,2,8,7,8,2,9,7,9,2,10,7,10,2,11,7,11,2,12,7,12,2,13,7,13,
        2,14,7,14,2,15,7,15,2,16,7,16,2,17,7,17,2,18,7,18,2,19,7,19,2,20,
        7,20,2,21,7,21,2,22,7,22,2,23,7,23,2,24,7,24,1,0,1,0,1,0,1,0,5,0,
        55,8,0,10,0,12,0,58,9,0,1,1,1,1,4,1,62,8,1,11,1,12,1,63,1,2,1,2,
        1,2,1,2,4,2,70,8,2,11,2,12,2,71,1,2,1,2,1,2,1,3,1,3,4,3,79,8,3,11,
        3,12,3,80,1,3,1,3,1,4,1,4,1,4,5,4,88,8,4,10,4,12,4,91,9,4,1,4,1,
        4,1,4,1,4,1,5,1,5,1,5,1,5,1,5,5,5,102,8,5,10,5,12,5,105,9,5,1,5,
        1,5,1,6,1,6,1,6,1,6,1,6,1,6,1,6,1,6,1,6,1,6,1,6,3,6,120,8,6,1,7,
        1,7,4,7,124,8,7,11,7,12,7,125,1,8,1,8,1,8,1,8,1,8,1,9,1,9,4,9,135,
        8,9,11,9,12,9,136,1,10,1,10,1,10,1,10,1,10,1,10,1,10,3,10,146,8,
        10,1,10,1,10,1,10,3,10,151,8,10,1,11,1,11,1,11,1,11,1,12,1,12,1,
        12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,3,12,170,8,
        12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,
        12,1,12,1,12,3,12,187,8,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,
        12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,
        12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,
        12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,
        12,1,12,1,12,1,12,5,12,239,8,12,10,12,12,12,242,9,12,1,13,1,13,1,
        13,3,13,247,8,13,1,13,3,13,250,8,13,1,14,1,14,1,14,1,14,1,15,1,15,
        1,15,1,15,3,15,260,8,15,1,15,1,15,1,16,1,16,1,16,5,16,267,8,16,10,
        16,12,16,270,9,16,1,17,1,17,1,17,1,18,1,18,1,18,1,19,1,19,1,20,1,
        20,1,21,1,21,1,22,1,22,1,23,1,23,1,24,1,24,1,24,0,1,24,25,0,2,4,
        6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,
        0,8,3,0,50,51,54,54,57,57,2,0,53,53,55,56,2,0,28,29,71,73,1,0,36,
        37,1,0,38,41,1,0,42,43,1,0,44,46,2,0,30,30,43,43,306,0,56,1,0,0,
        0,2,59,1,0,0,0,4,65,1,0,0,0,6,76,1,0,0,0,8,84,1,0,0,0,10,96,1,0,
        0,0,12,119,1,0,0,0,14,121,1,0,0,0,16,127,1,0,0,0,18,132,1,0,0,0,
        20,150,1,0,0,0,22,152,1,0,0,0,24,186,1,0,0,0,26,249,1,0,0,0,28,251,
        1,0,0,0,30,255,1,0,0,0,32,263,1,0,0,0,34,271,1,0,0,0,36,274,1,0,
        0,0,38,277,1,0,0,0,40,279,1,0,0,0,42,281,1,0,0,0,44,283,1,0,0,0,
        46,285,1,0,0,0,48,287,1,0,0,0,50,55,3,2,1,0,51,55,3,6,3,0,52,55,
        3,14,7,0,53,55,3,18,9,0,54,50,1,0,0,0,54,51,1,0,0,0,54,52,1,0,0,
        0,54,53,1,0,0,0,55,58,1,0,0,0,56,54,1,0,0,0,56,57,1,0,0,0,57,1,1,
        0,0,0,58,56,1,0,0,0,59,61,5,16,0,0,60,62,3,4,2,0,61,60,1,0,0,0,62,
        63,1,0,0,0,63,61,1,0,0,0,63,64,1,0,0,0,64,3,1,0,0,0,65,66,5,71,0,
        0,66,67,5,1,0,0,67,69,5,2,0,0,68,70,3,8,4,0,69,68,1,0,0,0,70,71,
        1,0,0,0,71,69,1,0,0,0,71,72,1,0,0,0,72,73,1,0,0,0,73,74,5,3,0,0,
        74,75,5,4,0,0,75,5,1,0,0,0,76,78,5,17,0,0,77,79,3,8,4,0,78,77,1,
        0,0,0,79,80,1,0,0,0,80,78,1,0,0,0,80,81,1,0,0,0,81,82,1,0,0,0,82,
        83,3,10,5,0,83,7,1,0,0,0,84,89,5,71,0,0,85,86,5,5,0,0,86,88,5,71,
        0,0,87,85,1,0,0,0,88,91,1,0,0,0,89,87,1,0,0,0,89,90,1,0,0,0,90,92,
        1,0,0,0,91,89,1,0,0,0,92,93,5,1,0,0,93,94,3,12,6,0,94,95,5,4,0,0,
        95,9,1,0,0,0,96,97,5,20,0,0,97,98,5,1,0,0,98,103,5,71,0,0,99,100,
        5,5,0,0,100,102,5,71,0,0,101,99,1,0,0,0,102,105,1,0,0,0,103,101,
        1,0,0,0,103,104,1,0,0,0,104,106,1,0,0,0,105,103,1,0,0,0,106,107,
        5,4,0,0,107,11,1,0,0,0,108,120,5,71,0,0,109,110,5,21,0,0,110,111,
        5,6,0,0,111,112,3,12,6,0,112,113,5,7,0,0,113,120,1,0,0,0,114,115,
        5,21,0,0,115,116,5,41,0,0,116,117,3,12,6,0,117,118,5,40,0,0,118,
        120,1,0,0,0,119,108,1,0,0,0,119,109,1,0,0,0,119,114,1,0,0,0,120,
        13,1,0,0,0,121,123,5,18,0,0,122,124,3,16,8,0,123,122,1,0,0,0,124,
        125,1,0,0,0,125,123,1,0,0,0,125,126,1,0,0,0,126,15,1,0,0,0,127,128,
        5,71,0,0,128,129,5,8,0,0,129,130,3,24,12,0,130,131,5,4,0,0,131,17,
        1,0,0,0,132,134,5,19,0,0,133,135,3,20,10,0,134,133,1,0,0,0,135,136,
        1,0,0,0,136,134,1,0,0,0,136,137,1,0,0,0,137,19,1,0,0,0,138,139,5,
        71,0,0,139,140,5,1,0,0,140,141,3,22,11,0,141,142,5,4,0,0,142,151,
        1,0,0,0,143,144,5,71,0,0,144,146,5,1,0,0,145,143,1,0,0,0,145,146,
        1,0,0,0,146,147,1,0,0,0,147,148,3,24,12,0,148,149,5,4,0,0,149,151,
        1,0,0,0,150,138,1,0,0,0,150,145,1,0,0,0,151,21,1,0,0,0,152,153,3,
        24,12,0,153,154,5,9,0,0,154,155,3,24,12,0,155,23,1,0,0,0,156,157,
        6,12,-1,0,157,187,3,26,13,0,158,159,5,71,0,0,159,160,5,10,0,0,160,
        161,3,28,14,0,161,162,5,11,0,0,162,163,5,10,0,0,163,164,3,24,12,
        0,164,165,5,11,0,0,165,187,1,0,0,0,166,167,5,71,0,0,167,169,5,10,
        0,0,168,170,3,32,16,0,169,168,1,0,0,0,169,170,1,0,0,0,170,171,1,
        0,0,0,171,187,5,11,0,0,172,173,5,43,0,0,173,187,3,24,12,19,174,175,
        5,42,0,0,175,187,3,24,12,18,176,177,5,30,0,0,177,187,3,24,12,17,
        178,179,3,34,17,0,179,180,3,24,12,6,180,187,1,0,0,0,181,182,5,10,
        0,0,182,183,3,24,12,0,183,184,5,11,0,0,184,187,1,0,0,0,185,187,3,
        38,19,0,186,156,1,0,0,0,186,158,1,0,0,0,186,166,1,0,0,0,186,172,
        1,0,0,0,186,174,1,0,0,0,186,176,1,0,0,0,186,178,1,0,0,0,186,181,
        1,0,0,0,186,185,1,0,0,0,187,240,1,0,0,0,188,189,10,16,0,0,189,190,
        3,46,23,0,190,191,3,24,12,17,191,239,1,0,0,0,192,193,10,15,0,0,193,
        194,3,44,22,0,194,195,3,24,12,16,195,239,1,0,0,0,196,197,10,14,0,
        0,197,198,5,34,0,0,198,239,3,24,12,15,199,200,10,13,0,0,200,201,
        5,35,0,0,201,239,3,24,12,14,202,203,10,12,0,0,203,204,3,42,21,0,
        204,205,3,24,12,13,205,239,1,0,0,0,206,207,10,11,0,0,207,208,3,40,
        20,0,208,209,3,24,12,12,209,239,1,0,0,0,210,211,10,10,0,0,211,212,
        5,31,0,0,212,239,3,24,12,11,213,214,10,9,0,0,214,215,5,33,0,0,215,
        239,3,24,12,10,216,217,10,8,0,0,217,218,5,32,0,0,218,239,3,24,12,
        9,219,220,10,7,0,0,220,221,3,36,18,0,221,222,3,24,12,8,222,239,1,
        0,0,0,223,224,10,5,0,0,224,225,5,23,0,0,225,239,3,24,12,6,226,227,
        10,4,0,0,227,228,5,24,0,0,228,239,3,24,12,5,229,230,10,3,0,0,230,
        231,5,13,0,0,231,232,3,24,12,0,232,233,5,1,0,0,233,234,3,24,12,4,
        234,239,1,0,0,0,235,236,10,20,0,0,236,237,5,12,0,0,237,239,5,71,
        0,0,238,188,1,0,0,0,238,192,1,0,0,0,238,196,1,0,0,0,238,199,1,0,
        0,0,238,202,1,0,0,0,238,206,1,0,0,0,238,210,1,0,0,0,238,213,1,0,
        0,0,238,216,1,0,0,0,238,219,1,0,0,0,238,223,1,0,0,0,238,226,1,0,
        0,0,238,229,1,0,0,0,238,235,1,0,0,0,239,242,1,0,0,0,240,238,1,0,
        0,0,240,241,1,0,0,0,241,25,1,0,0,0,242,240,1,0,0,0,243,250,5,60,
        0,0,244,246,5,2,0,0,245,247,3,32,16,0,246,245,1,0,0,0,246,247,1,
        0,0,0,247,248,1,0,0,0,248,250,5,3,0,0,249,243,1,0,0,0,249,244,1,
        0,0,0,250,27,1,0,0,0,251,252,5,71,0,0,252,253,5,1,0,0,253,254,3,
        24,12,0,254,29,1,0,0,0,255,256,5,14,0,0,256,259,5,73,0,0,257,258,
        5,5,0,0,258,260,5,73,0,0,259,257,1,0,0,0,259,260,1,0,0,0,260,261,
        1,0,0,0,261,262,5,15,0,0,262,31,1,0,0,0,263,268,3,24,12,0,264,265,
        5,5,0,0,265,267,3,24,12,0,266,264,1,0,0,0,267,270,1,0,0,0,268,266,
        1,0,0,0,268,269,1,0,0,0,269,33,1,0,0,0,270,268,1,0,0,0,271,272,7,
        0,0,0,272,273,3,30,15,0,273,35,1,0,0,0,274,275,7,1,0,0,275,276,3,
        30,15,0,276,37,1,0,0,0,277,278,7,2,0,0,278,39,1,0,0,0,279,280,7,
        3,0,0,280,41,1,0,0,0,281,282,7,4,0,0,282,43,1,0,0,0,283,284,7,5,
        0,0,284,45,1,0,0,0,285,286,7,6,0,0,286,47,1,0,0,0,287,288,7,7,0,
        0,288,49,1,0,0,0,20,54,56,63,71,80,89,103,119,125,136,145,150,169,
        186,238,240,246,249,259,268
    ]

class C2POParser ( Parser ):

    grammarFileName = "C2PO.g"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ "<INVALID>", "':'", "'{'", "'}'", "';'", "','", "'\\u27E8'", 
                     "'\\u27E9'", "'='", "'=>'", "'('", "')'", "'.'", "'?'", 
                     "'['", "']'", "'STRUCT'", "'VAR'", "'DEFINE'", "'SPEC'", 
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
                      "KW_STRUCT", "KW_VAR", "KW_DEF", "KW_SPEC", "KW_ORDER", 
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
    RULE_var_block = 3
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
    RULE_fo_binder = 14
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

    ruleNames =  [ "start", "struct_block", "struct", "var_block", "var_list", 
                   "order_list", "type", "def_block", "def", "spec_block", 
                   "spec", "contract", "expr", "set_expr", "fo_binder", 
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
    KW_VAR=17
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


        def var_block(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(C2POParser.Var_blockContext)
            else:
                return self.getTypedRuleContext(C2POParser.Var_blockContext,i)


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
                    self.var_block()
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


    class Var_blockContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def KW_VAR(self):
            return self.getToken(C2POParser.KW_VAR, 0)

        def order_list(self):
            return self.getTypedRuleContext(C2POParser.Order_listContext,0)


        def var_list(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(C2POParser.Var_listContext)
            else:
                return self.getTypedRuleContext(C2POParser.Var_listContext,i)


        def getRuleIndex(self):
            return C2POParser.RULE_var_block

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitVar_block" ):
                return visitor.visitVar_block(self)
            else:
                return visitor.visitChildren(self)




    def var_block(self):

        localctx = C2POParser.Var_blockContext(self, self._ctx, self.state)
        self.enterRule(localctx, 6, self.RULE_var_block)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 76
            self.match(C2POParser.KW_VAR)
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
            self.state = 84
            self.match(C2POParser.IDENTIFIER)
            self.state = 89
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==5:
                self.state = 85
                self.match(C2POParser.T__4)
                self.state = 86
                self.match(C2POParser.IDENTIFIER)
                self.state = 91
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 92
            self.match(C2POParser.T__0)
            self.state = 93
            self.type_()
            self.state = 94
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
            self.state = 96
            self.match(C2POParser.KW_ORDER)
            self.state = 97
            self.match(C2POParser.T__0)
            self.state = 98
            self.match(C2POParser.IDENTIFIER)
            self.state = 103
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==5:
                self.state = 99
                self.match(C2POParser.T__4)
                self.state = 100
                self.match(C2POParser.IDENTIFIER)
                self.state = 105
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 106
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
            self.state = 119
            self._errHandler.sync(self)
            la_ = self._interp.adaptivePredict(self._input,7,self._ctx)
            if la_ == 1:
                self.enterOuterAlt(localctx, 1)
                self.state = 108
                self.match(C2POParser.IDENTIFIER)
                pass

            elif la_ == 2:
                self.enterOuterAlt(localctx, 2)
                self.state = 109
                self.match(C2POParser.KW_SET)
                self.state = 110
                self.match(C2POParser.T__5)
                self.state = 111
                self.type_()
                self.state = 112
                self.match(C2POParser.T__6)
                pass

            elif la_ == 3:
                self.enterOuterAlt(localctx, 3)
                self.state = 114
                self.match(C2POParser.KW_SET)
                self.state = 115
                self.match(C2POParser.REL_LT)
                self.state = 116
                self.type_()
                self.state = 117
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
            self.state = 121
            self.match(C2POParser.KW_DEF)
            self.state = 123 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 122
                self.def_()
                self.state = 125 
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
            self.state = 127
            self.match(C2POParser.IDENTIFIER)
            self.state = 128
            self.match(C2POParser.T__7)
            self.state = 129
            self.expr(0)
            self.state = 130
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
            self.state = 132
            self.match(C2POParser.KW_SPEC)
            self.state = 134 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 133
                self.spec()
                self.state = 136 
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
            self.state = 150
            self._errHandler.sync(self)
            la_ = self._interp.adaptivePredict(self._input,11,self._ctx)
            if la_ == 1:
                self.enterOuterAlt(localctx, 1)
                self.state = 138
                self.match(C2POParser.IDENTIFIER)
                self.state = 139
                self.match(C2POParser.T__0)
                self.state = 140
                self.contract()
                self.state = 141
                self.match(C2POParser.T__3)
                pass

            elif la_ == 2:
                self.enterOuterAlt(localctx, 2)
                self.state = 145
                self._errHandler.sync(self)
                la_ = self._interp.adaptivePredict(self._input,10,self._ctx)
                if la_ == 1:
                    self.state = 143
                    self.match(C2POParser.IDENTIFIER)
                    self.state = 144
                    self.match(C2POParser.T__0)


                self.state = 147
                self.expr(0)
                self.state = 148
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
            self.state = 152
            self.expr(0)
            self.state = 153
            self.match(C2POParser.T__8)
            self.state = 154
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


    class FOExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a C2POParser.ExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def IDENTIFIER(self):
            return self.getToken(C2POParser.IDENTIFIER, 0)
        def fo_binder(self):
            return self.getTypedRuleContext(C2POParser.Fo_binderContext,0)

        def expr(self):
            return self.getTypedRuleContext(C2POParser.ExprContext,0)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitFOExpr" ):
                return visitor.visitFOExpr(self)
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
            self.state = 186
            self._errHandler.sync(self)
            la_ = self._interp.adaptivePredict(self._input,13,self._ctx)
            if la_ == 1:
                localctx = C2POParser.SetExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx

                self.state = 157
                self.set_expr()
                pass

            elif la_ == 2:
                localctx = C2POParser.FOExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 158
                self.match(C2POParser.IDENTIFIER)
                self.state = 159
                self.match(C2POParser.T__9)
                self.state = 160
                self.fo_binder()
                self.state = 161
                self.match(C2POParser.T__10)
                self.state = 162
                self.match(C2POParser.T__9)
                self.state = 163
                self.expr(0)
                self.state = 164
                self.match(C2POParser.T__10)
                pass

            elif la_ == 3:
                localctx = C2POParser.FuncExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 166
                self.match(C2POParser.IDENTIFIER)
                self.state = 167
                self.match(C2POParser.T__9)
                self.state = 169
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if ((_la) & ~0x3f) == 0 and ((1 << _la) & 1318441986931295236) != 0 or (((_la - 71)) & ~0x3f) == 0 and ((1 << (_la - 71)) & 7) != 0:
                    self.state = 168
                    self.expr_list()


                self.state = 171
                self.match(C2POParser.T__10)
                pass

            elif la_ == 4:
                localctx = C2POParser.UnaryExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 172
                self.match(C2POParser.ARITH_SUB)
                self.state = 173
                self.expr(19)
                pass

            elif la_ == 5:
                localctx = C2POParser.UnaryExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 174
                self.match(C2POParser.ARITH_ADD)
                self.state = 175
                self.expr(18)
                pass

            elif la_ == 6:
                localctx = C2POParser.UnaryExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 176
                self.match(C2POParser.BW_NEG)
                self.state = 177
                self.expr(17)
                pass

            elif la_ == 7:
                localctx = C2POParser.TLUnaryExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 178
                self.tl_unary_op()
                self.state = 179
                self.expr(6)
                pass

            elif la_ == 8:
                localctx = C2POParser.ParensExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 181
                self.match(C2POParser.T__9)
                self.state = 182
                self.expr(0)
                self.state = 183
                self.match(C2POParser.T__10)
                pass

            elif la_ == 9:
                localctx = C2POParser.LiteralExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 185
                self.literal()
                pass


            self._ctx.stop = self._input.LT(-1)
            self.state = 240
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,15,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    if self._parseListeners is not None:
                        self.triggerExitRuleEvent()
                    _prevctx = localctx
                    self.state = 238
                    self._errHandler.sync(self)
                    la_ = self._interp.adaptivePredict(self._input,14,self._ctx)
                    if la_ == 1:
                        localctx = C2POParser.ArithMulExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 188
                        if not self.precpred(self._ctx, 16):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 16)")
                        self.state = 189
                        self.arith_mul_op()
                        self.state = 190
                        self.expr(17)
                        pass

                    elif la_ == 2:
                        localctx = C2POParser.ArithAddExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 192
                        if not self.precpred(self._ctx, 15):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 15)")
                        self.state = 193
                        self.arith_add_op()
                        self.state = 194
                        self.expr(16)
                        pass

                    elif la_ == 3:
                        localctx = C2POParser.BWExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 196
                        if not self.precpred(self._ctx, 14):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 14)")
                        self.state = 197
                        self.match(C2POParser.BW_SHIFT_LEFT)
                        self.state = 198
                        self.expr(15)
                        pass

                    elif la_ == 4:
                        localctx = C2POParser.BWExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 199
                        if not self.precpred(self._ctx, 13):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 13)")
                        self.state = 200
                        self.match(C2POParser.BW_SHIFT_RIGHT)
                        self.state = 201
                        self.expr(14)
                        pass

                    elif la_ == 5:
                        localctx = C2POParser.RelExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 202
                        if not self.precpred(self._ctx, 12):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 12)")
                        self.state = 203
                        self.rel_ineq_op()
                        self.state = 204
                        self.expr(13)
                        pass

                    elif la_ == 6:
                        localctx = C2POParser.RelExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 206
                        if not self.precpred(self._ctx, 11):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 11)")
                        self.state = 207
                        self.rel_eq_op()
                        self.state = 208
                        self.expr(12)
                        pass

                    elif la_ == 7:
                        localctx = C2POParser.BWExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 210
                        if not self.precpred(self._ctx, 10):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 10)")
                        self.state = 211
                        self.match(C2POParser.BW_AND)
                        self.state = 212
                        self.expr(11)
                        pass

                    elif la_ == 8:
                        localctx = C2POParser.BWExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 213
                        if not self.precpred(self._ctx, 9):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 9)")
                        self.state = 214
                        self.match(C2POParser.BW_XOR)
                        self.state = 215
                        self.expr(10)
                        pass

                    elif la_ == 9:
                        localctx = C2POParser.BWExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 216
                        if not self.precpred(self._ctx, 8):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 8)")
                        self.state = 217
                        self.match(C2POParser.BW_OR)
                        self.state = 218
                        self.expr(9)
                        pass

                    elif la_ == 10:
                        localctx = C2POParser.TLBinExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 219
                        if not self.precpred(self._ctx, 7):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 7)")
                        self.state = 220
                        self.tl_bin_op()
                        self.state = 221
                        self.expr(8)
                        pass

                    elif la_ == 11:
                        localctx = C2POParser.LogBinExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 223
                        if not self.precpred(self._ctx, 5):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 5)")
                        self.state = 224
                        self.match(C2POParser.LOG_AND)
                        self.state = 225
                        self.expr(6)
                        pass

                    elif la_ == 12:
                        localctx = C2POParser.LogBinExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 226
                        if not self.precpred(self._ctx, 4):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 4)")
                        self.state = 227
                        self.match(C2POParser.LOG_OR)
                        self.state = 228
                        self.expr(5)
                        pass

                    elif la_ == 13:
                        localctx = C2POParser.TernaryExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 229
                        if not self.precpred(self._ctx, 3):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 3)")
                        self.state = 230
                        self.match(C2POParser.T__12)
                        self.state = 231
                        self.expr(0)
                        self.state = 232
                        self.match(C2POParser.T__0)
                        self.state = 233
                        self.expr(4)
                        pass

                    elif la_ == 14:
                        localctx = C2POParser.StructMemberExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 235
                        if not self.precpred(self._ctx, 20):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 20)")
                        self.state = 236
                        self.match(C2POParser.T__11)
                        self.state = 237
                        self.match(C2POParser.IDENTIFIER)
                        pass

             
                self.state = 242
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,15,self._ctx)

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
            self.state = 249
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [60]:
                self.enterOuterAlt(localctx, 1)
                self.state = 243
                self.match(C2POParser.SW_EMPTY_SET)
                pass
            elif token in [2]:
                self.enterOuterAlt(localctx, 2)
                self.state = 244
                self.match(C2POParser.T__1)
                self.state = 246
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if ((_la) & ~0x3f) == 0 and ((1 << _la) & 1318441986931295236) != 0 or (((_la - 71)) & ~0x3f) == 0 and ((1 << (_la - 71)) & 7) != 0:
                    self.state = 245
                    self.expr_list()


                self.state = 248
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


    class Fo_binderContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def IDENTIFIER(self):
            return self.getToken(C2POParser.IDENTIFIER, 0)

        def expr(self):
            return self.getTypedRuleContext(C2POParser.ExprContext,0)


        def getRuleIndex(self):
            return C2POParser.RULE_fo_binder

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitFo_binder" ):
                return visitor.visitFo_binder(self)
            else:
                return visitor.visitChildren(self)




    def fo_binder(self):

        localctx = C2POParser.Fo_binderContext(self, self._ctx, self.state)
        self.enterRule(localctx, 28, self.RULE_fo_binder)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 251
            self.match(C2POParser.IDENTIFIER)
            self.state = 252
            self.match(C2POParser.T__0)
            self.state = 253
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
            self.state = 255
            self.match(C2POParser.T__13)
            self.state = 256
            self.match(C2POParser.INT)
            self.state = 259
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==5:
                self.state = 257
                self.match(C2POParser.T__4)
                self.state = 258
                self.match(C2POParser.INT)


            self.state = 261
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
            self.state = 263
            self.expr(0)
            self.state = 268
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==5:
                self.state = 264
                self.match(C2POParser.T__4)
                self.state = 265
                self.expr(0)
                self.state = 270
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
            self.state = 271
            _la = self._input.LA(1)
            if not(((_la) & ~0x3f) == 0 and ((1 << _la) & 165507286305865728) != 0):
                self._errHandler.recoverInline(self)
            else:
                self._errHandler.reportMatch(self)
                self.consume()
            self.state = 272
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
            self.state = 274
            _la = self._input.LA(1)
            if not(((_la) & ~0x3f) == 0 and ((1 << _la) & 117093590311632896) != 0):
                self._errHandler.recoverInline(self)
            else:
                self._errHandler.reportMatch(self)
                self.consume()
            self.state = 275
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
            self.state = 277
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
            self.state = 279
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
            self.state = 281
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
            self.state = 283
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
            self.state = 285
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
            self.state = 287
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
         




