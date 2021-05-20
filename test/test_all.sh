#!/bin/sh

python3 TL_formula/genFormulas.py -r
python3 TL_formula/genFormulas.py -m
python3 Inputs/genInputs.py -r
python3 Inputs/genInputs.py -m
python3 Oracle/genOracle.py -r
python3 Oracle/genOracle.py -m

rm -rf results/c_version
echo "Hydra Subset"
python3 HydraSubset.py -v c
python3 HydraReport.py

rm -rf results/c_version
echo "Large FT Subset"
python3 LargeFtSubset.py -v c
python3 LargeFtReport.py

rm -rf results/c_version
echo "Large PT Subset"
python3 LargePtSubset.py -v c
python3 LargePtReport.py

rm -rf results/c_version
echo "Old FT Subset"
python3 OldFtSuiteSubset.py -v c
python3 OldFtSuiteReport.py

rm -rf results/c_version
