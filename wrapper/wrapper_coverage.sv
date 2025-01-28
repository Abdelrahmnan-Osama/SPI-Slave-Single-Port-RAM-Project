package wrapper_coverage_pkg;
  import uvm_pkg::*;
  import wrapper_seq_item_pkg::*;
  `include "uvm_macros.svh"

  class wrapper_coverage extends uvm_component;
    `uvm_component_utils(wrapper_coverage)

    wrapper_seq_item seq_item;
    uvm_analysis_export #(wrapper_seq_item) cov_export;
    uvm_tlm_analysis_fifo #(wrapper_seq_item) cov_fifo;

    covergroup cvr_gp;
      option.per_instance = 1;
      wrapper_select_cp: coverpoint seq_item.SS_n {
        // selected bin
        bins selected = {1'b0};
        // not selected bin
        bins not_selected = {1'b1};
      }

      MISO_cp: coverpoint seq_item.MISO {
        bins high = {1'b1};
        bins low = {1'b0};
        bins high_low = (1'b1 => 1'b0);
        bins low_high = (1'b0 => 1'b1);
      }

      MOSI_cp: coverpoint seq_item.MOSI {
        bins high = {1'b1};
        bins low = {1'b0};
        bins high_low = (1'b1 => 1'b0);
        bins low_high = (1'b0 => 1'b1);
      }


    endgroup

    function new(string name = "wrapper_coverage", uvm_component parent = null);
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
  endclass  //wrapper_coverage extends uvm_component
endpackage
