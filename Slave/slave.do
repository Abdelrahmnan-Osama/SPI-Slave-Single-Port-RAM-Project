vlib work
vlog -f src_files.list +cover -covercells
vsim +UVM_VERBOSITY=UVM_MEDIUM +UVM_NO_RELNOTES -voptargs=+acc work.top -classdebug -uvmcontrol=all -cover

run 0

add wave -position insertpoint  \
sim:/top/slaveif/SCK \
sim:/top/slaveif/rst_n \
sim:/top/slaveif/SS_n \
sim:/top/slaveif/MOSI \
sim:/top/slaveif/rx_data \
sim:/uvm_root/uvm_test_top/env/sb/rx_data_ref \
sim:/uvm_root/uvm_test_top/env/sb/SS_n_delayed \
sim:/uvm_root/uvm_test_top/env/sb/should_read \
sim:/top/slaveif/read_addr_received \
sim:/uvm_root/uvm_test_top/env/sb/addr_received \
sim:/uvm_root/uvm_test_top/env/sb/start_countdown \
sim:/uvm_root/uvm_test_top/env/sb/last_read \
sim:/top/DUT/wr_counter \
sim:/uvm_root/uvm_test_top/env/sb/wr_count \
sim:/top/DUT/rd_counter \
sim:/uvm_root/uvm_test_top/env/sb/rd_count \
sim:/top/DUT/cs \
sim:/top/DUT/ns \
sim:/top/slaveif/rx_valid \
sim:/top/slaveif/tx_data \
sim:/top/slaveif/tx_valid \
sim:/top/slaveif/MISO \
sim:/uvm_root/uvm_test_top/env/sb/MISO_ref 

add wave /top/DUT/slave_sva_inst/slave_not_selected_assertion \
/top/DUT/slave_sva_inst/read_operation_assertion \
/top/DUT/slave_sva_inst/write_addr_assertion \
/top/DUT/slave_sva_inst/read_addr_assertion \
/top/DUT/slave_sva_inst/write_data_assertion \
/top/DUT/slave_sva_inst/reset_assertion 

coverage exclude -src slave.sv -line 61 -code b
coverage exclude -src slave.sv -line 32 -code c
coverage exclude -src slave.sv -line 34 -code c
coverage exclude -src slave.sv -line 61 -code s

coverage save slave.ucdb -onexit
run -all
vcover report slave.ucdb -details -annotate -all -output coverage_rpt.txt