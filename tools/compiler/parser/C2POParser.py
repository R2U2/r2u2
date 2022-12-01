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
        4,1,71,278,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,2,6,7,
        6,2,7,7,7,2,8,7,8,2,9,7,9,2,10,7,10,2,11,7,11,2,12,7,12,2,13,7,13,
        2,14,7,14,2,15,7,15,2,16,7,16,2,17,7,17,2,18,7,18,2,19,7,19,2,20,
        7,20,2,21,7,21,2,22,7,22,2,23,7,23,1,0,1,0,1,0,1,0,5,0,53,8,0,10,
        0,12,0,56,9,0,1,1,1,1,4,1,60,8,1,11,1,12,1,61,1,2,1,2,1,2,1,2,4,
        2,68,8,2,11,2,12,2,69,1,2,1,2,1,2,1,3,1,3,4,3,77,8,3,11,3,12,3,78,
        1,4,1,4,1,4,5,4,84,8,4,10,4,12,4,87,9,4,1,4,1,4,1,4,1,4,1,5,1,5,
        1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,3,5,104,8,5,1,6,1,6,4,6,108,
        8,6,11,6,12,6,109,1,7,1,7,1,7,1,7,1,7,1,8,1,8,4,8,119,8,8,11,8,12,
        8,120,1,9,1,9,1,9,1,9,1,9,1,9,1,9,3,9,130,8,9,1,9,1,9,1,9,3,9,135,
        8,9,1,10,1,10,1,10,1,10,1,11,1,11,1,11,1,11,1,11,1,11,1,11,3,11,
        148,8,11,1,11,1,11,1,11,1,11,1,11,1,11,1,11,1,11,3,11,158,8,11,1,
        11,1,11,1,11,1,11,1,11,1,11,1,11,1,11,1,11,1,11,1,11,1,11,1,11,1,
        11,1,11,3,11,175,8,11,1,11,1,11,1,11,1,11,1,11,1,11,1,11,1,11,1,
        11,1,11,1,11,1,11,1,11,1,11,1,11,1,11,1,11,1,11,1,11,1,11,1,11,1,
        11,1,11,1,11,1,11,1,11,1,11,1,11,1,11,1,11,1,11,1,11,1,11,1,11,1,
        11,1,11,1,11,1,11,1,11,1,11,1,11,1,11,1,11,1,11,1,11,1,11,1,11,1,
        11,1,11,1,11,5,11,227,8,11,10,11,12,11,230,9,11,1,12,1,12,1,12,3,
        12,235,8,12,1,12,3,12,238,8,12,1,13,1,13,1,13,1,13,1,14,1,14,1,14,
        1,14,3,14,248,8,14,1,14,1,14,1,15,1,15,1,15,5,15,255,8,15,10,15,
        12,15,258,9,15,1,16,1,16,1,16,1,17,1,17,1,17,1,18,1,18,1,19,1,19,
        1,20,1,20,1,21,1,21,1,22,1,22,1,23,1,23,1,23,0,1,22,24,0,2,4,6,8,
        10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,0,8,3,0,
        48,49,52,52,55,55,2,0,51,51,53,54,2,0,26,27,67,69,1,0,34,35,1,0,
        36,39,1,0,40,41,1,0,42,44,2,0,28,28,41,41,295,0,54,1,0,0,0,2,57,
        1,0,0,0,4,63,1,0,0,0,6,74,1,0,0,0,8,80,1,0,0,0,10,103,1,0,0,0,12,
        105,1,0,0,0,14,111,1,0,0,0,16,116,1,0,0,0,18,134,1,0,0,0,20,136,
        1,0,0,0,22,174,1,0,0,0,24,237,1,0,0,0,26,239,1,0,0,0,28,243,1,0,
        0,0,30,251,1,0,0,0,32,259,1,0,0,0,34,262,1,0,0,0,36,265,1,0,0,0,
        38,267,1,0,0,0,40,269,1,0,0,0,42,271,1,0,0,0,44,273,1,0,0,0,46,275,
        1,0,0,0,48,53,3,2,1,0,49,53,3,6,3,0,50,53,3,12,6,0,51,53,3,16,8,
        0,52,48,1,0,0,0,52,49,1,0,0,0,52,50,1,0,0,0,52,51,1,0,0,0,53,56,
        1,0,0,0,54,52,1,0,0,0,54,55,1,0,0,0,55,1,1,0,0,0,56,54,1,0,0,0,57,
        59,5,16,0,0,58,60,3,4,2,0,59,58,1,0,0,0,60,61,1,0,0,0,61,59,1,0,
        0,0,61,62,1,0,0,0,62,3,1,0,0,0,63,64,5,67,0,0,64,65,5,1,0,0,65,67,
        5,2,0,0,66,68,3,8,4,0,67,66,1,0,0,0,68,69,1,0,0,0,69,67,1,0,0,0,
        69,70,1,0,0,0,70,71,1,0,0,0,71,72,5,3,0,0,72,73,5,4,0,0,73,5,1,0,
        0,0,74,76,5,17,0,0,75,77,3,8,4,0,76,75,1,0,0,0,77,78,1,0,0,0,78,
        76,1,0,0,0,78,79,1,0,0,0,79,7,1,0,0,0,80,85,5,67,0,0,81,82,5,5,0,
        0,82,84,5,67,0,0,83,81,1,0,0,0,84,87,1,0,0,0,85,83,1,0,0,0,85,86,
        1,0,0,0,86,88,1,0,0,0,87,85,1,0,0,0,88,89,5,1,0,0,89,90,3,10,5,0,
        90,91,5,4,0,0,91,9,1,0,0,0,92,104,5,67,0,0,93,94,5,67,0,0,94,95,
        5,6,0,0,95,96,3,10,5,0,96,97,5,7,0,0,97,104,1,0,0,0,98,99,5,67,0,
        0,99,100,5,39,0,0,100,101,3,10,5,0,101,102,5,38,0,0,102,104,1,0,
        0,0,103,92,1,0,0,0,103,93,1,0,0,0,103,98,1,0,0,0,104,11,1,0,0,0,
        105,107,5,18,0,0,106,108,3,14,7,0,107,106,1,0,0,0,108,109,1,0,0,
        0,109,107,1,0,0,0,109,110,1,0,0,0,110,13,1,0,0,0,111,112,5,67,0,
        0,112,113,5,8,0,0,113,114,3,22,11,0,114,115,5,4,0,0,115,15,1,0,0,
        0,116,118,5,19,0,0,117,119,3,18,9,0,118,117,1,0,0,0,119,120,1,0,
        0,0,120,118,1,0,0,0,120,121,1,0,0,0,121,17,1,0,0,0,122,123,5,67,
        0,0,123,124,5,1,0,0,124,125,3,20,10,0,125,126,5,4,0,0,126,135,1,
        0,0,0,127,128,5,67,0,0,128,130,5,1,0,0,129,127,1,0,0,0,129,130,1,
        0,0,0,130,131,1,0,0,0,131,132,3,22,11,0,132,133,5,4,0,0,133,135,
        1,0,0,0,134,122,1,0,0,0,134,129,1,0,0,0,135,19,1,0,0,0,136,137,3,
        22,11,0,137,138,5,9,0,0,138,139,3,22,11,0,139,21,1,0,0,0,140,141,
        6,11,-1,0,141,175,3,24,12,0,142,143,5,67,0,0,143,144,5,10,0,0,144,
        147,3,26,13,0,145,146,5,5,0,0,146,148,3,22,11,0,147,145,1,0,0,0,
        147,148,1,0,0,0,148,149,1,0,0,0,149,150,5,11,0,0,150,151,5,10,0,
        0,151,152,3,22,11,0,152,153,5,11,0,0,153,175,1,0,0,0,154,155,5,67,
        0,0,155,157,5,10,0,0,156,158,3,30,15,0,157,156,1,0,0,0,157,158,1,
        0,0,0,158,159,1,0,0,0,159,175,5,11,0,0,160,161,5,41,0,0,161,175,
        3,22,11,19,162,163,5,40,0,0,163,175,3,22,11,18,164,165,5,28,0,0,
        165,175,3,22,11,17,166,167,3,32,16,0,167,168,3,22,11,6,168,175,1,
        0,0,0,169,170,5,10,0,0,170,171,3,22,11,0,171,172,5,11,0,0,172,175,
        1,0,0,0,173,175,3,36,18,0,174,140,1,0,0,0,174,142,1,0,0,0,174,154,
        1,0,0,0,174,160,1,0,0,0,174,162,1,0,0,0,174,164,1,0,0,0,174,166,
        1,0,0,0,174,169,1,0,0,0,174,173,1,0,0,0,175,228,1,0,0,0,176,177,
        10,16,0,0,177,178,3,44,22,0,178,179,3,22,11,17,179,227,1,0,0,0,180,
        181,10,15,0,0,181,182,3,42,21,0,182,183,3,22,11,16,183,227,1,0,0,
        0,184,185,10,14,0,0,185,186,5,32,0,0,186,227,3,22,11,15,187,188,
        10,13,0,0,188,189,5,33,0,0,189,227,3,22,11,14,190,191,10,12,0,0,
        191,192,3,40,20,0,192,193,3,22,11,13,193,227,1,0,0,0,194,195,10,
        11,0,0,195,196,3,38,19,0,196,197,3,22,11,12,197,227,1,0,0,0,198,
        199,10,10,0,0,199,200,5,29,0,0,200,227,3,22,11,11,201,202,10,9,0,
        0,202,203,5,31,0,0,203,227,3,22,11,10,204,205,10,8,0,0,205,206,5,
        30,0,0,206,227,3,22,11,9,207,208,10,7,0,0,208,209,3,34,17,0,209,
        210,3,22,11,8,210,227,1,0,0,0,211,212,10,5,0,0,212,213,5,21,0,0,
        213,227,3,22,11,6,214,215,10,4,0,0,215,216,5,22,0,0,216,227,3,22,
        11,5,217,218,10,3,0,0,218,219,5,13,0,0,219,220,3,22,11,0,220,221,
        5,1,0,0,221,222,3,22,11,4,222,227,1,0,0,0,223,224,10,20,0,0,224,
        225,5,12,0,0,225,227,5,67,0,0,226,176,1,0,0,0,226,180,1,0,0,0,226,
        184,1,0,0,0,226,187,1,0,0,0,226,190,1,0,0,0,226,194,1,0,0,0,226,
        198,1,0,0,0,226,201,1,0,0,0,226,204,1,0,0,0,226,207,1,0,0,0,226,
        211,1,0,0,0,226,214,1,0,0,0,226,217,1,0,0,0,226,223,1,0,0,0,227,
        230,1,0,0,0,228,226,1,0,0,0,228,229,1,0,0,0,229,23,1,0,0,0,230,228,
        1,0,0,0,231,238,5,56,0,0,232,234,5,2,0,0,233,235,3,30,15,0,234,233,
        1,0,0,0,234,235,1,0,0,0,235,236,1,0,0,0,236,238,5,3,0,0,237,231,
        1,0,0,0,237,232,1,0,0,0,238,25,1,0,0,0,239,240,5,67,0,0,240,241,
        5,1,0,0,241,242,3,22,11,0,242,27,1,0,0,0,243,244,5,14,0,0,244,247,
        5,69,0,0,245,246,5,5,0,0,246,248,5,69,0,0,247,245,1,0,0,0,247,248,
        1,0,0,0,248,249,1,0,0,0,249,250,5,15,0,0,250,29,1,0,0,0,251,256,
        3,22,11,0,252,253,5,5,0,0,253,255,3,22,11,0,254,252,1,0,0,0,255,
        258,1,0,0,0,256,254,1,0,0,0,256,257,1,0,0,0,257,31,1,0,0,0,258,256,
        1,0,0,0,259,260,7,0,0,0,260,261,3,28,14,0,261,33,1,0,0,0,262,263,
        7,1,0,0,263,264,3,28,14,0,264,35,1,0,0,0,265,266,7,2,0,0,266,37,
        1,0,0,0,267,268,7,3,0,0,268,39,1,0,0,0,269,270,7,4,0,0,270,41,1,
        0,0,0,271,272,7,5,0,0,272,43,1,0,0,0,273,274,7,6,0,0,274,45,1,0,
        0,0,275,276,7,7,0,0,276,47,1,0,0,0,20,52,54,61,69,78,85,103,109,
        120,129,134,147,157,174,226,228,234,237,247,256
    ]

class C2POParser ( Parser ):

    grammarFileName = "C2PO.g"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ "<INVALID>", "':'", "'{'", "'}'", "';'", "','", "'\\u27E8'", 
                     "'\\u27E9'", "'='", "'=>'", "'('", "')'", "'.'", "'?'", 
                     "'['", "']'", "'STRUCT'", "'INPUT'", "'DEFINE'", "'SPEC'", 
                     "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                     "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                     "'~'", "'&'", "'|'", "'^'", "'<<'", "'>>'", "'=='", 
                     "<INVALID>", "<INVALID>", "<INVALID>", "'>'", "'<'", 
                     "'+'", "'-'", "<INVALID>", "<INVALID>", "'%'", "'**'", 
                     "'\\u221A'", "<INVALID>", "<INVALID>", "<INVALID>", 
                     "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                     "<INVALID>", "<INVALID>", "'\\u2205'", "'\\u2208'", 
                     "'\\u2282'", "'\\u2286'", "'\\u2211'", "'\\u220F'", 
                     "'\\u22C3'", "'\\u22C2'", "'\\u22C0'", "'\\u22C1'", 
                     "'\\u00D7'" ]

    symbolicNames = [ "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "KW_STRUCT", "KW_INPUT", "KW_DEF", "KW_SPEC", "LOG_NEG", 
                      "LOG_AND", "LOG_OR", "LOG_XOR", "LOG_IMPL", "LOG_IFF", 
                      "TRUE", "FALSE", "BW_NEG", "BW_AND", "BW_OR", "BW_XOR", 
                      "BW_SHIFT_LEFT", "BW_SHIFT_RIGHT", "REL_EQ", "REL_NEQ", 
                      "REL_GTE", "REL_LTE", "REL_GT", "REL_LT", "ARITH_ADD", 
                      "ARITH_SUB", "ARITH_MUL", "ARITH_DIV", "ARITH_MOD", 
                      "ARITH_POW", "ARITH_SQRT", "ARITH_PM", "TL_GLOBAL", 
                      "TL_FUTURE", "TL_NEXT", "TL_SINCE", "TL_ONCE", "TL_UNTIL", 
                      "TL_RELEASE", "TL_HISTORICAL", "SW_EMPTY_SET", "SW_MEMBER", 
                      "SW_SUBSET", "SW_SUBSETEQ", "SW_SUM", "SW_PROD", "SW_UNION", 
                      "SW_INTERSECTION", "SW_AND", "SW_OR", "SW_CTPROD", 
                      "IDENTIFIER", "FLOAT", "INT", "COMMENT", "WS" ]

    RULE_start = 0
    RULE_struct_block = 1
    RULE_struct = 2
    RULE_input_block = 3
    RULE_var_list = 4
    RULE_type = 5
    RULE_def_block = 6
    RULE_def = 7
    RULE_spec_block = 8
    RULE_spec = 9
    RULE_contract = 10
    RULE_expr = 11
    RULE_set_expr = 12
    RULE_set_agg_binder = 13
    RULE_interval = 14
    RULE_expr_list = 15
    RULE_tl_unary_op = 16
    RULE_tl_bin_op = 17
    RULE_literal = 18
    RULE_rel_eq_op = 19
    RULE_rel_ineq_op = 20
    RULE_arith_add_op = 21
    RULE_arith_mul_op = 22
    RULE_unary_op = 23

    ruleNames =  [ "start", "struct_block", "struct", "input_block", "var_list", 
                   "type", "def_block", "def", "spec_block", "spec", "contract", 
                   "expr", "set_expr", "set_agg_binder", "interval", "expr_list", 
                   "tl_unary_op", "tl_bin_op", "literal", "rel_eq_op", "rel_ineq_op", 
                   "arith_add_op", "arith_mul_op", "unary_op" ]

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
    LOG_NEG=20
    LOG_AND=21
    LOG_OR=22
    LOG_XOR=23
    LOG_IMPL=24
    LOG_IFF=25
    TRUE=26
    FALSE=27
    BW_NEG=28
    BW_AND=29
    BW_OR=30
    BW_XOR=31
    BW_SHIFT_LEFT=32
    BW_SHIFT_RIGHT=33
    REL_EQ=34
    REL_NEQ=35
    REL_GTE=36
    REL_LTE=37
    REL_GT=38
    REL_LT=39
    ARITH_ADD=40
    ARITH_SUB=41
    ARITH_MUL=42
    ARITH_DIV=43
    ARITH_MOD=44
    ARITH_POW=45
    ARITH_SQRT=46
    ARITH_PM=47
    TL_GLOBAL=48
    TL_FUTURE=49
    TL_NEXT=50
    TL_SINCE=51
    TL_ONCE=52
    TL_UNTIL=53
    TL_RELEASE=54
    TL_HISTORICAL=55
    SW_EMPTY_SET=56
    SW_MEMBER=57
    SW_SUBSET=58
    SW_SUBSETEQ=59
    SW_SUM=60
    SW_PROD=61
    SW_UNION=62
    SW_INTERSECTION=63
    SW_AND=64
    SW_OR=65
    SW_CTPROD=66
    IDENTIFIER=67
    FLOAT=68
    INT=69
    COMMENT=70
    WS=71

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
            self.state = 54
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while ((_la) & ~0x3f) == 0 and ((1 << _la) & 983040) != 0:
                self.state = 52
                self._errHandler.sync(self)
                token = self._input.LA(1)
                if token in [16]:
                    self.state = 48
                    self.struct_block()
                    pass
                elif token in [17]:
                    self.state = 49
                    self.input_block()
                    pass
                elif token in [18]:
                    self.state = 50
                    self.def_block()
                    pass
                elif token in [19]:
                    self.state = 51
                    self.spec_block()
                    pass
                else:
                    raise NoViableAltException(self)

                self.state = 56
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
            self.state = 57
            self.match(C2POParser.KW_STRUCT)
            self.state = 59 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 58
                self.struct()
                self.state = 61 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (_la==67):
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
            self.state = 63
            self.match(C2POParser.IDENTIFIER)
            self.state = 64
            self.match(C2POParser.T__0)
            self.state = 65
            self.match(C2POParser.T__1)
            self.state = 67 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 66
                self.var_list()
                self.state = 69 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (_la==67):
                    break

            self.state = 71
            self.match(C2POParser.T__2)
            self.state = 72
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
            self.state = 74
            self.match(C2POParser.KW_INPUT)
            self.state = 76 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 75
                self.var_list()
                self.state = 78 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (_la==67):
                    break

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
            self.state = 80
            self.match(C2POParser.IDENTIFIER)
            self.state = 85
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==5:
                self.state = 81
                self.match(C2POParser.T__4)
                self.state = 82
                self.match(C2POParser.IDENTIFIER)
                self.state = 87
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 88
            self.match(C2POParser.T__0)
            self.state = 89
            self.type_()
            self.state = 90
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
        self.enterRule(localctx, 10, self.RULE_type)
        try:
            self.state = 103
            self._errHandler.sync(self)
            la_ = self._interp.adaptivePredict(self._input,6,self._ctx)
            if la_ == 1:
                self.enterOuterAlt(localctx, 1)
                self.state = 92
                self.match(C2POParser.IDENTIFIER)
                pass

            elif la_ == 2:
                self.enterOuterAlt(localctx, 2)
                self.state = 93
                self.match(C2POParser.IDENTIFIER)
                self.state = 94
                self.match(C2POParser.T__5)
                self.state = 95
                self.type_()
                self.state = 96
                self.match(C2POParser.T__6)
                pass

            elif la_ == 3:
                self.enterOuterAlt(localctx, 3)
                self.state = 98
                self.match(C2POParser.IDENTIFIER)
                self.state = 99
                self.match(C2POParser.REL_LT)
                self.state = 100
                self.type_()
                self.state = 101
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
        self.enterRule(localctx, 12, self.RULE_def_block)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 105
            self.match(C2POParser.KW_DEF)
            self.state = 107 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 106
                self.def_()
                self.state = 109 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (_la==67):
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
        self.enterRule(localctx, 14, self.RULE_def)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 111
            self.match(C2POParser.IDENTIFIER)
            self.state = 112
            self.match(C2POParser.T__7)
            self.state = 113
            self.expr(0)
            self.state = 114
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
        self.enterRule(localctx, 16, self.RULE_spec_block)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 116
            self.match(C2POParser.KW_SPEC)
            self.state = 118 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 117
                self.spec()
                self.state = 120 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (((_la) & ~0x3f) == 0 and ((1 << _la) & 113437714619040772) != 0 or (((_la - 67)) & ~0x3f) == 0 and ((1 << (_la - 67)) & 7) != 0):
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
        self.enterRule(localctx, 18, self.RULE_spec)
        try:
            self.state = 134
            self._errHandler.sync(self)
            la_ = self._interp.adaptivePredict(self._input,10,self._ctx)
            if la_ == 1:
                self.enterOuterAlt(localctx, 1)
                self.state = 122
                self.match(C2POParser.IDENTIFIER)
                self.state = 123
                self.match(C2POParser.T__0)
                self.state = 124
                self.contract()
                self.state = 125
                self.match(C2POParser.T__3)
                pass

            elif la_ == 2:
                self.enterOuterAlt(localctx, 2)
                self.state = 129
                self._errHandler.sync(self)
                la_ = self._interp.adaptivePredict(self._input,9,self._ctx)
                if la_ == 1:
                    self.state = 127
                    self.match(C2POParser.IDENTIFIER)
                    self.state = 128
                    self.match(C2POParser.T__0)


                self.state = 131
                self.expr(0)
                self.state = 132
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
        self.enterRule(localctx, 20, self.RULE_contract)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 136
            self.expr(0)
            self.state = 137
            self.match(C2POParser.T__8)
            self.state = 138
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

        def expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(C2POParser.ExprContext)
            else:
                return self.getTypedRuleContext(C2POParser.ExprContext,i)


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
        _startState = 22
        self.enterRecursionRule(localctx, 22, self.RULE_expr, _p)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 174
            self._errHandler.sync(self)
            la_ = self._interp.adaptivePredict(self._input,13,self._ctx)
            if la_ == 1:
                localctx = C2POParser.SetExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx

                self.state = 141
                self.set_expr()
                pass

            elif la_ == 2:
                localctx = C2POParser.SetAggExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 142
                self.match(C2POParser.IDENTIFIER)
                self.state = 143
                self.match(C2POParser.T__9)
                self.state = 144
                self.set_agg_binder()
                self.state = 147
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if _la==5:
                    self.state = 145
                    self.match(C2POParser.T__4)
                    self.state = 146
                    self.expr(0)


                self.state = 149
                self.match(C2POParser.T__10)
                self.state = 150
                self.match(C2POParser.T__9)
                self.state = 151
                self.expr(0)
                self.state = 152
                self.match(C2POParser.T__10)
                pass

            elif la_ == 3:
                localctx = C2POParser.FuncExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 154
                self.match(C2POParser.IDENTIFIER)
                self.state = 155
                self.match(C2POParser.T__9)
                self.state = 157
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if ((_la) & ~0x3f) == 0 and ((1 << _la) & 113437714619040772) != 0 or (((_la - 67)) & ~0x3f) == 0 and ((1 << (_la - 67)) & 7) != 0:
                    self.state = 156
                    self.expr_list()


                self.state = 159
                self.match(C2POParser.T__10)
                pass

            elif la_ == 4:
                localctx = C2POParser.UnaryExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 160
                self.match(C2POParser.ARITH_SUB)
                self.state = 161
                self.expr(19)
                pass

            elif la_ == 5:
                localctx = C2POParser.UnaryExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 162
                self.match(C2POParser.ARITH_ADD)
                self.state = 163
                self.expr(18)
                pass

            elif la_ == 6:
                localctx = C2POParser.UnaryExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 164
                self.match(C2POParser.BW_NEG)
                self.state = 165
                self.expr(17)
                pass

            elif la_ == 7:
                localctx = C2POParser.TLUnaryExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 166
                self.tl_unary_op()
                self.state = 167
                self.expr(6)
                pass

            elif la_ == 8:
                localctx = C2POParser.ParensExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 169
                self.match(C2POParser.T__9)
                self.state = 170
                self.expr(0)
                self.state = 171
                self.match(C2POParser.T__10)
                pass

            elif la_ == 9:
                localctx = C2POParser.LiteralExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 173
                self.literal()
                pass


            self._ctx.stop = self._input.LT(-1)
            self.state = 228
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,15,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    if self._parseListeners is not None:
                        self.triggerExitRuleEvent()
                    _prevctx = localctx
                    self.state = 226
                    self._errHandler.sync(self)
                    la_ = self._interp.adaptivePredict(self._input,14,self._ctx)
                    if la_ == 1:
                        localctx = C2POParser.ArithMulExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 176
                        if not self.precpred(self._ctx, 16):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 16)")
                        self.state = 177
                        self.arith_mul_op()
                        self.state = 178
                        self.expr(17)
                        pass

                    elif la_ == 2:
                        localctx = C2POParser.ArithAddExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 180
                        if not self.precpred(self._ctx, 15):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 15)")
                        self.state = 181
                        self.arith_add_op()
                        self.state = 182
                        self.expr(16)
                        pass

                    elif la_ == 3:
                        localctx = C2POParser.BWExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 184
                        if not self.precpred(self._ctx, 14):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 14)")
                        self.state = 185
                        self.match(C2POParser.BW_SHIFT_LEFT)
                        self.state = 186
                        self.expr(15)
                        pass

                    elif la_ == 4:
                        localctx = C2POParser.BWExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 187
                        if not self.precpred(self._ctx, 13):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 13)")
                        self.state = 188
                        self.match(C2POParser.BW_SHIFT_RIGHT)
                        self.state = 189
                        self.expr(14)
                        pass

                    elif la_ == 5:
                        localctx = C2POParser.RelExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 190
                        if not self.precpred(self._ctx, 12):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 12)")
                        self.state = 191
                        self.rel_ineq_op()
                        self.state = 192
                        self.expr(13)
                        pass

                    elif la_ == 6:
                        localctx = C2POParser.RelExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 194
                        if not self.precpred(self._ctx, 11):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 11)")
                        self.state = 195
                        self.rel_eq_op()
                        self.state = 196
                        self.expr(12)
                        pass

                    elif la_ == 7:
                        localctx = C2POParser.BWExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 198
                        if not self.precpred(self._ctx, 10):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 10)")
                        self.state = 199
                        self.match(C2POParser.BW_AND)
                        self.state = 200
                        self.expr(11)
                        pass

                    elif la_ == 8:
                        localctx = C2POParser.BWExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 201
                        if not self.precpred(self._ctx, 9):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 9)")
                        self.state = 202
                        self.match(C2POParser.BW_XOR)
                        self.state = 203
                        self.expr(10)
                        pass

                    elif la_ == 9:
                        localctx = C2POParser.BWExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 204
                        if not self.precpred(self._ctx, 8):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 8)")
                        self.state = 205
                        self.match(C2POParser.BW_OR)
                        self.state = 206
                        self.expr(9)
                        pass

                    elif la_ == 10:
                        localctx = C2POParser.TLBinExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 207
                        if not self.precpred(self._ctx, 7):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 7)")
                        self.state = 208
                        self.tl_bin_op()
                        self.state = 209
                        self.expr(8)
                        pass

                    elif la_ == 11:
                        localctx = C2POParser.LogBinExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 211
                        if not self.precpred(self._ctx, 5):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 5)")
                        self.state = 212
                        self.match(C2POParser.LOG_AND)
                        self.state = 213
                        self.expr(6)
                        pass

                    elif la_ == 12:
                        localctx = C2POParser.LogBinExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 214
                        if not self.precpred(self._ctx, 4):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 4)")
                        self.state = 215
                        self.match(C2POParser.LOG_OR)
                        self.state = 216
                        self.expr(5)
                        pass

                    elif la_ == 13:
                        localctx = C2POParser.TernaryExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 217
                        if not self.precpred(self._ctx, 3):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 3)")
                        self.state = 218
                        self.match(C2POParser.T__12)
                        self.state = 219
                        self.expr(0)
                        self.state = 220
                        self.match(C2POParser.T__0)
                        self.state = 221
                        self.expr(4)
                        pass

                    elif la_ == 14:
                        localctx = C2POParser.StructMemberExprContext(self, C2POParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 223
                        if not self.precpred(self._ctx, 20):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 20)")
                        self.state = 224
                        self.match(C2POParser.T__11)
                        self.state = 225
                        self.match(C2POParser.IDENTIFIER)
                        pass

             
                self.state = 230
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
        self.enterRule(localctx, 24, self.RULE_set_expr)
        self._la = 0 # Token type
        try:
            self.state = 237
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [56]:
                self.enterOuterAlt(localctx, 1)
                self.state = 231
                self.match(C2POParser.SW_EMPTY_SET)
                pass
            elif token in [2]:
                self.enterOuterAlt(localctx, 2)
                self.state = 232
                self.match(C2POParser.T__1)
                self.state = 234
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if ((_la) & ~0x3f) == 0 and ((1 << _la) & 113437714619040772) != 0 or (((_la - 67)) & ~0x3f) == 0 and ((1 << (_la - 67)) & 7) != 0:
                    self.state = 233
                    self.expr_list()


                self.state = 236
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
        self.enterRule(localctx, 26, self.RULE_set_agg_binder)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 239
            self.match(C2POParser.IDENTIFIER)
            self.state = 240
            self.match(C2POParser.T__0)
            self.state = 241
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
        self.enterRule(localctx, 28, self.RULE_interval)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 243
            self.match(C2POParser.T__13)
            self.state = 244
            self.match(C2POParser.INT)
            self.state = 247
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==5:
                self.state = 245
                self.match(C2POParser.T__4)
                self.state = 246
                self.match(C2POParser.INT)


            self.state = 249
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
        self.enterRule(localctx, 30, self.RULE_expr_list)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 251
            self.expr(0)
            self.state = 256
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==5:
                self.state = 252
                self.match(C2POParser.T__4)
                self.state = 253
                self.expr(0)
                self.state = 258
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
        self.enterRule(localctx, 32, self.RULE_tl_unary_op)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 259
            _la = self._input.LA(1)
            if not(((_la) & ~0x3f) == 0 and ((1 << _la) & 41376821576466432) != 0):
                self._errHandler.recoverInline(self)
            else:
                self._errHandler.reportMatch(self)
                self.consume()
            self.state = 260
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
        self.enterRule(localctx, 34, self.RULE_tl_bin_op)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 262
            _la = self._input.LA(1)
            if not(((_la) & ~0x3f) == 0 and ((1 << _la) & 29273397577908224) != 0):
                self._errHandler.recoverInline(self)
            else:
                self._errHandler.reportMatch(self)
                self.consume()
            self.state = 263
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
        self.enterRule(localctx, 36, self.RULE_literal)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 265
            _la = self._input.LA(1)
            if not((((_la - 26)) & ~0x3f) == 0 and ((1 << (_la - 26)) & 15393162788867) != 0):
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
        self.enterRule(localctx, 38, self.RULE_rel_eq_op)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 267
            _la = self._input.LA(1)
            if not(_la==34 or _la==35):
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
        self.enterRule(localctx, 40, self.RULE_rel_ineq_op)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 269
            _la = self._input.LA(1)
            if not(((_la) & ~0x3f) == 0 and ((1 << _la) & 1030792151040) != 0):
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
        self.enterRule(localctx, 42, self.RULE_arith_add_op)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 271
            _la = self._input.LA(1)
            if not(_la==40 or _la==41):
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
        self.enterRule(localctx, 44, self.RULE_arith_mul_op)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 273
            _la = self._input.LA(1)
            if not(((_la) & ~0x3f) == 0 and ((1 << _la) & 30786325577728) != 0):
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
        self.enterRule(localctx, 46, self.RULE_unary_op)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 275
            _la = self._input.LA(1)
            if not(_la==28 or _la==41):
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
        self._predicates[11] = self.expr_sempred
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
         




