vlib work
vlog -f src_files.list +cover -covercells
vsim -suppress vsim-3829 +UVM_VERBOSITY=UVM_MEDIUM +UVM_NO_RELNOTES -voptargs=+acc work.top -classdebug -uvmcontrol=all -cover

run 0

add wave -position insertpoint  \
sim:/top/wif/clk \
sim:/top/wif/rst_n \
sim:/top/wif/SS_n \
sim:/top/wif/MOSI \
sim:/top/wif/MISO \
sim:/uvm_root/uvm_test_top/w_env/sb/MISO_ref 

coverage exclude -src slave.sv -line 78 -code b
coverage exclude -src slave.sv -line 49 -code c
coverage exclude -src slave.sv -line 51 -code c
coverage exclude -src slave.sv -line 78 -code s

coverage save wrapper.ucdb -onexit
run -all
vcover report wrapper.ucdb -details -annotate -all -output coverage_rpt.txt