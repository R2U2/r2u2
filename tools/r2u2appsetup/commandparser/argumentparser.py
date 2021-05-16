import argparse
parser = argparse.ArgumentParser(description='accept and launch subcommands')
parser.add_argument('--version', action='version', version='%(prog)s 1.0')
parser.parse_args()
