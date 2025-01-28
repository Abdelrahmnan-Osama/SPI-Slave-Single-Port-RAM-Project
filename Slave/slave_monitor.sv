package slave_monitor_pkg;
  import slave_seq_item_pkg::*;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  class slave_monitor extends uvm_monitor;
    `uvm_component_utils(slave_monitor)

    virtual slave_if slave_vif;
    slave_seq_item rsp_seq_item;
    uvm_analysis_port #(slave_seq_item) mon_ap;

    function new(string name = "slave_monitor", uvm_component parent = null);
      super.new(name, parent);
    endfunction  //new()

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      mon_ap = new("mon_ap", this);
    endfunction

    virtual task run_phase(uvm_phase phase);
      super.run_phase(phase);

      forever begin
        rsp_seq_item = slave_seq_item::type_id::create("rsp_seq_item");

        @(negedge slave_vif.SCK);
        rsp_seq_item.rst_n    = slave_vif.rst_n;
        rsp_seq_item.SS_n     = slave_vif.SS_n;
        rsp_seq_item.rx_valid = slave_vif.rx_valid;
        rsp_seq_item.tx_valid = slave_vif.tx_valid;
        rsp_seq_item.rx_data  = slave_vif.rx_data;
        rsp_seq_item.tx_data  = slave_vif.tx_data;
        rsp_seq_item.MOSI     = slave_vif.MOSI;
        rsp_seq_item.MISO     = slave_vif.MISO;

        mon_ap.write(rsp_seq_item);
        `uvm_info("run_phase", rsp_seq_item.convert2string(), UVM_HIGH)
      end

    endtask
  endclass  //slave_monitor extends uvm_monitor
endpackage
