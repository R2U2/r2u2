C2PO="../compiler/c2po.py"
R2U2="../monitors/c/build/r2u2"

python3 $C2PO --trace agc.csv agc.c2po
$R2U2 spec.bin agc.csv

python3 $C2PO --booleanizer --trace arrays.csv arrays.c2po
$R2U2 spec.bin arrays.csv

python3 $C2PO --booleanizer --map cav.map cav.c2po
$R2U2 spec.bin cav.csv

python3 $C2PO --trace set_agg.csv set_agg.c2po
$R2U2 spec.bin set_agg.csv

python3 $C2PO --trace simple.csv simple.c2po
$R2U2 spec.bin simple.csv

python3 $C2PO --trace struct.csv struct.c2po
$R2U2 spec.bin struct.csv

rm spec.bin