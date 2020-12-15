import argparse
from r2u2test import r2u2test

#create main parser
parser = argparse.ArgumentParser(description='accept subcommands to compile and run R2U2')
parser.add_argument('--version', action='version', version='%(prog)s 1.0')

#create subparsers
subparsers = parser.add_subparsers(title='subcommands', description='r2u2plot, r2u2trace, r2u2prep, r2u2test')
#r2u2plot subparser
parser_plot = subparsers.add_parser('r2u2plot', help='produces trace-verdict output graphs')
parser_plot.add_argument('values', action='append')
parser_plot.add_argument('verdicts', action='append')
#parser_plot.set_defaults(func=r2u2plot)
#r2u2prep subparser
parser_prep = subparsers.add_parser('r2u2prep', help='configures r2u2')
parser_prep.add_argument('formula')
#parser_prep.set_defaults(func=r2u2prep)
#r2u2test subparser
parser_test = subparsers.add_parser('r2u2test', help='runs r2u2 test suite')
parser_test.add_argument('subset')
parser_test.add_argument('version')
parser_test.set_defaults(func=r2u2test)
#r2u2trace subparser
parser_trace = subparsers.add_parser('r2u2trace', help='runs trace file expansion/minification')
parser_trace.add_argument('filename')
#parser_trace.set_defaults(func=r2u2prep)

args = parser.parse_args()

args.func(args)






