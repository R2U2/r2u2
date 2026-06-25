C2PO="../compiler/c2po.py"
R2U2="../monitors/c/build/r2u2"

echo "Running AGC example"
python3 $C2PO --trace agc.csv --spec agc.c2po
$R2U2 spec.bin agc.csv

echo "Running Arrays example"
python3 $C2PO --booleanizer --trace arrays.csv --spec arrays.c2po
$R2U2 spec.bin arrays.csv

echo "Running CAV example"
python3 $C2PO --booleanizer --map cav.map --spec cav.c2po
$R2U2 spec.bin cav.csv

echo "Running Set Aggregation example"
python3 $C2PO --trace set_agg.csv --spec set_agg.c2po
$R2U2 spec.bin set_agg.csv

echo "Running Simple example"
python3 $C2PO --script simple.cmd
$R2U2 spec.bin simple.csv

echo "Running Struct example"
python3 $C2PO --trace struct.csv --spec struct.c2po
$R2U2 spec.bin struct.csv

rm spec.bin