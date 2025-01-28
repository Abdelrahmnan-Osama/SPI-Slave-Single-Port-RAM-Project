package slave_coverage_pkg;
  import uvm_pkg::*;
  import slave_seq_item_pkg::*;
  `include "uvm_macros.svh"

  class slave_coverage extends uvm_component;
    `uvm_component_utils(slave_coverage)

    slave_seq_item seq_item;
    uvm_analysis_export #(slave_seq_item) cov_export;
    uvm_tlm_analysis_fifo #(slave_seq_item) cov_fifo;

    covergroup cvr_gp;
      option.per_instance = 1;
      slave_select_cp: coverpoint seq_item.SS_n {
        // selected bin
        bins selected = {1'b0};
        // not selected bin
        bins not_selected = {1'b1};
      }

      MISO_cp: coverpoint seq_item.MISO {
        // high bin
        bins high = {1'b1};
        // low bin
        bins low = {1'b0};
      }

      rx_opcode_cp: coverpoint seq_item.rx_data[9:8] {
        bins wr_addr = {2'b00};
        bins wr_op = {2'b01};
        bins rd_addr = {2'b10};
        bins rd_op = {2'b11};
        bins comp_rd_op = (2'b10 => 2'b11);
        bins comp_wr_op = (2'b00 => 2'b01);
      //option.weight = 0;
      }

      rx_valid_cp: coverpoint seq_item.rx_valid {
        // valid bin
        bins valid = {1'b1};
        // invalid bin
        bins invalid = {1'b0};
      }

      tx_valid_cp: coverpoint seq_item.tx_valid {
        // valid bin
        bins valid = {1'b1};
        // invalid bin
        bins invalid = {1'b0};
      //option.weight = 0;
      }

      tx_data_cp: coverpoint seq_item.tx_data {
        // bin for all values
        bins any_data = {[0 : 255]};
      //option.weight = 0;
      }

      rx_opcode_valid: cross rx_opcode_cp, rx_valid_cp{
        ignore_bins complete_valid_read = binsof(rx_opcode_cp.comp_rd_op) && binsof(rx_valid_cp.valid);
        ignore_bins complete_valid_write = binsof(rx_opcode_cp.comp_wr_op) && binsof(rx_valid_cp.valid);
      }

      tx_data_valid: cross tx_data_cp, tx_valid_cp;

    endgroup

    function new(string name = "slave_coverage", uvm_component parent = null);
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
  endclass  //slave_coverage extends uvm_component
endpackage
