onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /mac3_tb/s_clk
add wave -noupdate /mac3_tb/s_rst_n
add wave -noupdate /mac3_tb/s_sample_clk
add wave -noupdate /mac3_tb/s_data_in_1
add wave -noupdate /mac3_tb/s_data_in_2
add wave -noupdate /mac3_tb/s_data_in_3
add wave -noupdate /mac3_tb/s_data_out
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {1668 ns} 0}
quietly wave cursor active 0
configure wave -namecolwidth 181
configure wave -valuecolwidth 453
configure wave -justifyvalue left
configure wave -signalnamewidth 0
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ns
update
WaveRestoreZoom {1355 ns} {4016 ns}
