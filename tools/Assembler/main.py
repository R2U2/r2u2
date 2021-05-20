import argparse

from config import *
from atas import *
from ftas import *
from ptas import *

def main(conf, prev_header, new_header, ptasm, ftasm, ftscqasm, atasm, ts_ext,
         gen_dir, no_binaries):

    print('Generating configuration files')
    parse_config(conf)
    check_updates(prev_header)
    gen_config(new_header)

    assemble_pt(ptasm, ts_ext, gen_dir, no_binaries)
    assemble_ft(ftasm, ftscqasm, ts_ext, gen_dir, no_binaries)
    assemble_at(atasm, gen_dir, no_binaries)

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("conf", help="r2u2 config file")
    parser.add_argument("prev_header", help="location of previous R2U2Config.h")
    parser.add_argument("new_header", help="location of new R2U2Config.h")
    parser.add_argument("ptasm", help="past time assembly file")
    parser.add_argument("ftasm", help="future time assembly file")
    parser.add_argument("ftscqasm", help="future time scq assembly file")
    parser.add_argument("atasm", help="atomic checker assembly file")
    parser.add_argument("ts_ext", help="timestamp width extend byte")
    parser.add_argument("gen_dir", help="directory to generate files")
    parser.add_argument("no_binaries", help="generate config.c file in place of binaries")
    args = parser.parse_args()
    main(args.conf, args.prev_header, args.new_header, args.ptasm, args.ftasm,
         args.ftscqasm, args.atasm, args.ts_ext, args.gen_dir, args.no_binaries)
