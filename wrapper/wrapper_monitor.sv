package wrapper_monitor_pkg;
  import wrapper_seq_item_pkg::*;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  class wrapper_monitor extends uvm_monitor;
    `uvm_component_utils(wrapper_monitor)

    virtual wrapper_if wrapper_vif;
    wrapper_seq_item rsp_seq_item;
    uvm_analysis_port #(wrapper_seq_item) mon_ap;

    function new(string name = "wrapper_monitor", uvm_component parent = null);
      super.new(name, parent);
    endfunction  //new()

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      mon_ap = new("mon_ap", this);
    endfunction

    virtual task run_phase(uvm_phase phase);
      super.run_phase(phase);

      forever begin
        rsp_seq_item = wrapper_seq_item::type_id::create("rsp_seq_item");

        @(negedge wrapper_vif.clk);
        rsp_seq_item.rst_n = wrapper_vif.rst_n;
        rsp_seq_item.SS_n  = wrapper_vif.SS_n;
        rsp_seq_item.MOSI  = wrapper_vif.MOSI;
        rsp_seq_item.MISO  = wrapper_vif.MISO;

        mon_ap.write(rsp_seq_item);
        `uvm_info("run_phase", rsp_seq_item.convert2string(), UVM_HIGH)
      end

    endtask
  endclass  //wrapper_monitor extends uvm_monitor
endpackage
