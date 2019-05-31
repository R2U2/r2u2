#!/bin/bash
cat casestudy.ftasm | python ftas.py casestudy
mv casestudy.fti imem.imem.int
mv casestudy.ftm imem.imem
mv ./imem.* ../../Hardware/hdl/ftMuMonitor/sim/testbench
