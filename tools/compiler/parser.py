#type: ignore
from logging import getLogger

from .sly import Lexer, Parser
from .ast import *
from .util import *

logger = getLogger(logger_name)

class C2POLexer(Lexer):

    # Set of token names.   This is always required
    tokens = { KW_STRUCT, KW_INPUT, KW_DEFINE, KW_SPEC,
               LOG_NEG, LOG_AND, LOG_OR, LOG_XOR, LOG_IMPL, LOG_IFF,
               BW_NEG, BW_AND, BW_OR, BW_XOR, BW_SHIFT_LEFT, BW_SHIFT_RIGHT,
               REL_EQ, REL_NEQ, REL_GTE, REL_LTE, REL_GT, REL_LT,
               ARITH_ADD, ARITH_SUB, ARITH_MUL, ARITH_DIV, ARITH_MOD, ARITH_POW, ARITH_SQRT, ARITH_PM,
               ASSIGN, CONTRACT_ASSIGN, SYMBOL, FLOAT, INT, QUEST, SEMI, COLON, DOT, COMMA, 
               LBRACK, RBRACK, LBRACE, RBRACE, LPAREN, RPAREN }

    # String containing ignored characters between tokens
    ignore = ' \t'
    ignore_comment = r'--.*'
    ignore_newline = r'\n+'

    REL_NEQ = r'!=|≠' # longer tokens must come first
    FLOAT   = r'-?[1-9]+\.\d+'
    INT     = r'-?[1-9][0-9]*|0'

    # Propositional logic ops/literals
    LOG_NEG  = r'!|¬'
    LOG_AND  = r'&&|∧'
    LOG_OR   = r'\|\||∨'
    LOG_XOR  = r'XOR|⊕'
    LOG_IMPL = r'->|→'
    LOG_IFF  = r'<->|↔'

    # Bitwise ops
    BW_NEG          = r'~'
    BW_AND          = r'&' 
    BW_OR           = r'\|' 
    BW_XOR          = r'\^' 
    BW_SHIFT_LEFT   = r'<<'
    BW_SHIFT_RIGHT  = r'>>'

    # Relational ops
    REL_EQ  = r'=='
    REL_GTE = r'>=|≥'
    REL_LTE = r'<=|≤' 
    REL_GT  = r'>'
    REL_LT  = r'<'

    # Arithmetic ops
    ARITH_ADD   = r'\+'
    ARITH_SUB   = r'-'
    ARITH_MUL   = r'\*|•|⋅'
    ARITH_DIV   = r'/|÷'
    ARITH_MOD   = r'%'
    ARITH_POW   = r'\*\*'
    ARITH_SQRT  = r'√'
    ARITH_PM    = r'\+/-|±'

    # Others
    CONTRACT_ASSIGN = r'=>'
    ASSIGN  = r'='
    SYMBOL  = r'[a-zA-Z_][a-zA-Z0-9_]*'
    QUEST   = r'\?'
    SEMI    = r';'
    COLON   = r':'
    DOT     = r'\.'
    COMMA   = r','
    LBRACK  = r'\['
    RBRACK  = r'\]'
    LBRACE  = r'\{'
    RBRACE  = r'\}'
    LPAREN  = r'\('
    RPAREN  = r'\)'

    # Keywords
    SYMBOL['STRUCT'] = KW_STRUCT
    SYMBOL['INPUT'] = KW_INPUT
    SYMBOL['DEFINE'] = KW_DEFINE
    SYMBOL['SPEC'] = KW_SPEC

    # Extra action for newlines
    def ignore_newline(self, t):
        self.lineno += t.value.count('\n')

    def error(self, t):
        logger.error(f'{self.lineno}: Illegal character \'%s\' {t.value[0]}')
        self.index += 1


class C2POParser(Parser):
    tokens = C2POLexer.tokens

    precedence = (
        ('left', REL_GT, REL_LT, REL_GTE, REL_LTE),
        ('left', REL_EQ, REL_NEQ),
        ('left', LOG_AND),
    )

    def __init__(self) -> None:
        super().__init__()
        self.structs: StructDict = {}
        self.vars: dict[str,Type] = {}
        self.defs: dict[str,AST] = {}
        self.spec_num: int = 0
        self.status = True

        # Initialize special structs/functions
        self.structs['Set'] = {'set':NOTYPE(),'size':UINT64()}

    @_('program struct_block',
       'program input_block',
       'program define_block',
       'program spec_block',
       '')
    def program(self, p):
        logger.info('program')

    @_('KW_STRUCT struct struct_list')
    def struct_block(self, p):
        logger.info('struct_block')

    @_('struct_list struct', '')
    def struct_list(self, p):
        logger.info('struct_list')

    @_('SYMBOL COLON LBRACE var_list RBRACE SEMI')
    def struct(self, p):
        logger.info('struct')

    @_('KW_INPUT var_list')
    def input_block(self, p):
        logger.info('input_block')

    @_('SYMBOL symbol_list COLON type SEMI')
    def var_list(self, p):
        logger.info('var_list')

    @_('symbol_list COMMA SYMBOL', '')
    def symbol_list(self, p):
        logger.info('symbol_list')

    @_('SYMBOL', 'SYMBOL REL_LT type REL_GT')
    def type(self, p):
        logger.info('type')

    @_('KW_DEFINE definition definition_list')
    def define_block(self, p):
        logger.info('defin_block')

    @_('definition_list definition', '')
    def definition_list(self, p):
        logger.info('definition_list')

    @_('SYMBOL ASSIGN expr SEMI')
    def definition(self, p):
        logger.info('definition')

    @_('KW_SPEC spec')
    def spec_block(self, p):
        logger.info('spec_block')

    @_('SYMBOL COLON expr SEMI',
       'expr SEMI')
    def spec(self, p):
        logger.info('spec')

    @_('expr REL_GT expr', 
       'expr REL_EQ expr',
       'expr LOG_AND expr',
       'LPAREN expr RPAREN',
       'SYMBOL',
       'INT')
    def expr(self, p):
        logger.info('expr')
