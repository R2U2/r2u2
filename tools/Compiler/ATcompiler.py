import os
import re

__AbsolutePath__ = os.path.dirname(os.path.abspath(__file__))+'/'
__DirBinaryPath__ = __AbsolutePath__ + '../binary_files/'

class AT:

    def __init__(self, AT):
        self.status = 'pass'
        self.instructions = {}
        self.parse_mappings(AT)
        self.gen_assembly()

    def parse_mappings(self, input):
        # use regex to parse atomic mappings, lex/yacc is overkill
        for line in input.split(';'):
            if re.fullmatch('\s*', line):
                break

            filters = ['bool','int','double','rate']
            instr = []

            # Construct regex search strings
            atom_search_str = '\A\s*a\d+\s*(?=:=)'

            filter_search_str = '(?<=:=)\s*'
            for f in range(0,len(filters)):
                filter_search_str += '('+filters[f]+')'
                if f is not len(filters)-1:
                    filter_search_str += '|'

            signal_search_str = '(?<=\()\s*\d+\s*(?=\))'
            cond_search_str = '(?<=\))\s*[<>=]=?\s*'
            const_search_str = '(?<=[<>=])\s*\d+\s*\Z'

            # Example input:
            # a43 := rate(56) >= 76;
            atom = re.search(atom_search_str, line) # a0, a35, etc.
            filter = re.search(filter_search_str, line) # rate, abs, etc.
            signal = re.search(signal_search_str, line) # 0, 3, 56, etc.
            cond = re.search(cond_search_str, line) # ==, >=, >, etc.
            const = re.search(const_search_str, line) # 0, 3, 56, etc.

            if atom is None:
                print('Error: invalid atomic name in mapping ' + line)
            if filter is None:
                print('Error: invalid filter application in mapping ' + line)
            if signal is None:
                print('Error: invalid signal name in mapping ' + line)
            if cond is None:
                print('Error: invalid conditional in mapping ' + line)
            if const is None:
                print('Error: invalid constant in mapping ' + line)
            if atom is None or filter is None or signal is None or cond is None or const is None:
                # report all errors before returing
                self.status = 'syntax_err'
                return

            instr.append(filter.group().strip())
            instr.append(signal.group().strip())
            instr.append(cond.group().strip())
            instr.append(const.group().strip())

            self.instructions[atom.group().strip()] = instr


    def gen_assembly(self):
        s = ''
        for atom, instr in self.instructions.items():
            s += atom + ' ' + instr[0] + ' ' + instr[1] + ' ' + instr[2] + ' ' + instr[3] + '\n'
        s = s[:len(s)-1] # remove last newline

        print(s)
        with open(__DirBinaryPath__ + 'at.asm',"w+") as f:
            f.write(s)
