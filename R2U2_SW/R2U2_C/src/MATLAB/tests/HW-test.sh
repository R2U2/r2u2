#!/bin/bash

PATH=$1
cd $2/R2U2-HW//Software/ftAssembler
mv $3.fts casestudy.ftasm
sed '/^#/ d; s/ //g; /^$/d' $4.dat > atomic.trc
cat casestudy.ftasm | python ftas.py casestudy
mv casestudy.fti imem.imem.int
mv casestudy.ftm imem.imem
mv atomic.trc imem.* $2/R2U2-HW/Hardware/hdl/ftMuMonitor/sim/testbench
cd $2/R2U2-HW/Hardware/hdl/ftMuMonitor/vivado
echo -e "\
set sim_out_path \"$2/R2U2-HW/Hardware/hdl/ftMuMonitor/vivado/FT_Monitor/FT_Monitor.sim/sim_1/behav\"\n\
cd $2/R2U2-HW/Hardware/hdl/ftMuMonitor/vivado\n\
source -quiet FT_Monitor.tcl\n\
launch_simulation\n\
run 600 us\n\
close_sim\
" > gen_sim.tcl
cat gen_sim.tcl
vivado -mode batch -source gen_sim.tcl 
rm gen_sim.tcl
cat $2/R2U2-HW/Hardware/hdl/ftMuMonitor/vivado/FT_Monitor/FT_Monitor.sim/sim_1/behav/async_out.txt