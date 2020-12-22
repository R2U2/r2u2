#!/bin/sh

cd Inputs
python genInputs.py -r
python genInputs.py -m
cd ..

cd TL_formula
python genFormulas.py -r
python genFormulas.py -m
cd ..

cd Oracle
python genOracle.py -r
python genOracle.py -m
cd ..

python HydraSubset.py -r c
python HydraSubset.py -v c
python HydraReport.py

python LargeFtSubset.py -r c
python LargeFtSubset.py -v c
python LargeFtReport.py


python LargePtSubset.py -r c
python LargePtSubset.py -v c
python LargePtReport.py

python LargePtSubset.py -r c
python LargePtSubset.py -v c
python LargePtReport.py

python OldFtSuiteSubset.py -r c
python OldFtSuiteSubset.py -v c
python OldFtSuiteReport.py
