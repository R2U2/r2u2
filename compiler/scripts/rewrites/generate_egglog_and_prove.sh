#!/bin/bash
python3 generate_equiv_files.py rewrites.json equiv/
python3 generate_egglog.py equiv/ rewrites.json /opt/compiler/c2po/egglog/
./generate_smt2_equiv.sh equiv/ smt2/ /opt/compiler/c2po.py
./prove.sh smt2/ 600 24
