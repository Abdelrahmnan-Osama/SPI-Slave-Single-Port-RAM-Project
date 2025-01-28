package ram_coverage_pkg;
  import uvm_pkg::*;
  import ram_seq_item_pkg::*;
  `include "uvm_macros.svh"

  class ram_coverage extends uvm_component;
    `uvm_component_utils(ram_coverage)

    ram_seq_item seq_item;
    uvm_analysis_export #(ram_seq_item) cov_export;
    uvm_tlm_analysis_fifo #(ram_seq_item) cov_fifo;

    covergroup cvr_gp;
      option.per_instance = 1;
      opcode: coverpoint seq_item.din[9:8] {
        bins wr_addr = {2'b00};
        bins wr_op = {2'b01};
        bins rd_addr = {2'b10};
        bins rd_op = {2'b11};
        option.weight = 0;
      }

      rx_valid: coverpoint seq_item.rx_valid {
        bins valid = {1'b1}; bins not_valid = {1'b0}; option.weight = 0;
      }

      opcode_valid: cross opcode, rx_valid;

    endgroup

    function new(string name = "ram_coverage", uvm_component parent = null);
      super.new(name, parent);
      cvr_gp = new();
    endfunction  //new()

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      cov_export = new("cov_export", this);
      cov_fifo   = new("cov_fifo", this);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      cov_export.connect(cov_fifo.analysis_export);
    endfunction


    virtual task run_phase(uvm_phase phase);
      super.run_phase(phase);
      forever begin
        cov_fifo.get(seq_item);
        cvr_gp.sample();
      end
    endtask
  endclass  //ram_coverage extends uvm_component
endpackage
