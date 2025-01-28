vlib work
vlog -f src_files.list +define+SIM +cover -covercells
vsim -suppress vsim-3829 +UVM_VERBOSITY=UVM_MEDIUM +UVM_NO_RELNOTES -voptargs=+acc work.top -classdebug -uvmcontrol=all -cover

run 0

add wave -position insertpoint  \
sim:/top/ramif/clk \
sim:/top/ramif/rst_n \
sim:/top/ramif/din \
sim:/top/ramif/rx_valid \
sim:/top/ramif/dout \
sim:/uvm_root/uvm_test_top/env/sb/dout_ref \
sim:/top/ramif/tx_valid \
sim:/top/DUT/addr \
sim:/top/DUT/mem

add wave /top/DUT/address_updated_assertion \
/top/DUT/address_unchanged_assertion \
/top/DUT/ram_sva_inst/output_valid_assertion \
/top/DUT/ram_sva_inst/output_invalid_assertion \
/top/DUT/ram_sva_inst/reset_assertion


coverage save ram.ucdb -onexit
run -all
vcover report ram.ucdb -details -annotate -all -output coverage_rpt.txt