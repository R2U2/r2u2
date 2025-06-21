# The results have the following encodings:
#   - UFLIA (control)
#   - QF_UFLIA
#   - QF_BV (linear)
#   - QF_BV (linear, incremental)
#   - QF_BV (logarithmic)
#   - QF_BV (logarithmic, incremental)

# Eacu encoding was run over the following benchmarks, with each having 10,000 formulas a piece:
#   - random-10
#   - random-100
#   - random-1000
#   - random-10000

# Each plot has cumulative time on the x axis, number of formulas solved on the y axis

# First generate virtual best for each encoding/benchmark pair
python3 vb.py plot/uflia.random-10.txt results/vb.uflia.random-10.csv
python3 vb.py plot/uflia.random-100.txt results/vb.uflia.random-100.csv
python3 vb.py plot/uflia.random-1000.txt results/vb.uflia.random-1000.csv
python3 vb.py plot/uflia.random-10000.txt results/vb.uflia.random-10000.csv

python3 vb.py plot/qf_uflia.random-10.txt results/vb.qf_uflia.random-10.csv
python3 vb.py plot/qf_uflia.random-100.txt results/vb.qf_uflia.random-100.csv
python3 vb.py plot/qf_uflia.random-1000.txt results/vb.qf_uflia.random-1000.csv
python3 vb.py plot/qf_uflia.random-10000.txt results/vb.qf_uflia.random-10000.csv

python3 vb.py plot/qf_bv.random-10.txt results/vb.qf_bv.random-10.csv
python3 vb.py plot/qf_bv.random-100.txt results/vb.qf_bv.random-100.csv
python3 vb.py plot/qf_bv.random-1000.txt results/vb.qf_bv.random-1000.csv
python3 vb.py plot/qf_bv.random-10000.txt results/vb.qf_bv.random-10000.csv
python3 vb.py plot/qf_bv_incr.random-1000.txt results/vb.qf_bv_incr.random-1000.csv
python3 vb.py plot/qf_bv_incr.random-10000.txt results/vb.qf_bv_incr.random-10000.csv

python3 vb.py plot/qf_bv_log.random-10.txt results/vb.qf_bv_log.random-10.csv
python3 vb.py plot/qf_bv_log.random-100.txt results/vb.qf_bv_log.random-100.csv
python3 vb.py plot/qf_bv_log.random-1000.txt results/vb.qf_bv_log.random-1000.csv
python3 vb.py plot/qf_bv_log.random-10000.txt results/vb.qf_bv_log.random-10000.csv
python3 vb.py plot/qf_bv_log_incr.random-1000.txt results/vb.qf_bv_log_incr.random-1000.csv
python3 vb.py plot/qf_bv_log_incr.random-10000.txt results/vb.qf_bv_log_incr.random-10000.csv

# Then plot the stuff
python3 cactus.py plot/random-10.txt random-10.png
python3 cactus.py plot/random-100.txt random-100.png
python3 cactus.py plot/random-1000.txt random-1000.png
python3 cactus.py plot/random-10000.txt random-10000.png
python3 cactus.py plot/qf_bv.txt qf_bv.png