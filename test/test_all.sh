#!/bin/sh

python3 TL_formula/genFormulas.py -r
python3 TL_formula/genFormulas.py -m
python3 Inputs/genInputs.py -r
python3 Inputs/genInputs.py -m
python3 Oracle/genOracle.py -r
python3 Oracle/genOracle.py -m

rm -rf results/c_version
echo "FT Subset"
python3 Subset/FT_Subset.py -v c
python3 Report/FT_Report.py
rm -rf results/c_version

rm -rf results/c_version
echo "Large FT Subset"
python3 Subset/LargeFtSubset.py -v c
python3 Report/LargeFtReport.py

rm -rf results/c_version
echo "Large PT Subset"
python3 Subset/LargePtSubset.py -v c
python3 Report/LargePtReport.py

echo "FT/PT Subset"
python3 Subset/FT_PT_Subset.py -v c
python3 Report/FT_PT_Report.py

rm -rf results/c_version
