import os
import re

__AbsolutePath__ = os.path.dirname(os.path.abspath(__file__))+'/'
__DirBinaryPath__ = __AbsolutePath__ + '../binary_files/'

class AT:

    def __init__(self, AT):
        self.status = 'pass'
        self.instructions = {}
        self.parse(AT)
        self.gen_assembly()

    def tokenize(self, line):
        filters = ['bool','int','double','rate','abs_diff_angle','movavg']
        token_spec = [
            ('ATOM',   r'a\d+'),
            ('ASSIGN', r':='),
            ('FILTER', r'|'.join(filters)),
            ('NUMBER', r'\d+(\.\d*)?'),
            ('COND',   r'[<>=]=*'),
            ('LPAREN', r'\('),
            ('RPAREN', r'\)'),
            ('COMMA',  r','),
            ('SKIP',   r'\s+'),
            ('ERROR',  r'.')
        ]
        tok_re = '|'.join('(?P<%s>%s)' % pair for pair in token_spec)
        tokens = []
        for tok in re.finditer(tok_re, line):
            type = tok.lastgroup
            value = tok.group()
            if type == 'SKIP':
                pass
            elif type == 'ERROR':
                print('Syntax error in AT expression: ' + line)
            else:
                tokens.append([type, value])
        return tokens

    def parse(self, input):
        for line in input.split(';'):
            if re.fullmatch('\s*', line):
                break

            tokens = self.tokenize(line)

            prev_type = 'BEGIN'
            arg = '0'
            for tok in tokens:
                type = tok[0]
                value = str(tok[1])
                if type == 'ERROR':
                    self.status = 'syntax_err'
                    return
                if prev_type == 'BEGIN' and type == 'ATOM':
                    atom = value
                elif prev_type == 'ATOM' and type == 'ASSIGN':
                    pass
                elif prev_type == 'ASSIGN' and type == 'FILTER':
                    filter = value
                elif prev_type == 'FILTER' and type == 'LPAREN':
                    pass
                elif prev_type == 'LPAREN' and type == 'NUMBER':
                    signal = value
                elif prev_type == 'NUMBER' and type == 'COMMA':
                    pass
                elif prev_type == 'COMMA' and type == 'NUMBER':
                    arg = value
                elif prev_type == 'NUMBER' and type == 'RPAREN':
                    pass
                elif prev_type == 'RPAREN' and type == 'COND':
                    cond = value
                elif prev_type == 'COND' and type == 'NUMBER':
                    const = value
                else:
                    print('Syntax error in AT expression: ' + line)
                    self.status = 'syntax_err'
                    return
                prev_type = type

            instr = [filter, signal, arg, cond, const]

            self.instructions[atom] = instr

    def gen_assembly(self):
        s = ''
        for atom, instr in self.instructions.items():
            s += atom + ' ' + instr[0] + ' ' + instr[1] + ' ' + instr[2] + ' ' \
                + instr[3] + ' ' + instr[4] + '\n'
        s = s[:len(s)-1] # remove last newline

        with open(__DirBinaryPath__ + 'at.asm',"w+") as f:
            f.write(s)
