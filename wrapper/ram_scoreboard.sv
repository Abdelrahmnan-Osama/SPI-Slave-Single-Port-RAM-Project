package ram_scoreboard_pkg;
  import uvm_pkg::*;
  import ram_seq_item_pkg::*;
  `include "uvm_macros.svh"

  class ram_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(ram_scoreboard)

    parameter ram_WIDTH = 16;
    parameter ram_DEPTH = 8;

    uvm_analysis_export #(ram_seq_item) sb_export;
    uvm_tlm_analysis_fifo #(ram_seq_item) sb_fifo;
    ram_seq_item seq_item;

    bit [9:0] din_delayed;
    bit rx_valid_delayed;
    logic [7:0] dout_ref;
    logic [7:0] ram[logic [7:0]];
    logic [7:0] addr;

    int correct_count, error_count;

    function new(string name = "ram_scoreboard", uvm_component parent = null);
      super.new(name, parent);
    endfunction  //new()


    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      sb_export = new("sb_export", this);
      sb_fifo   = new("sb_fifo", this);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      sb_export.connect(sb_fifo.analysis_export);
    endfunction

    virtual task run_phase(uvm_phase phase);
      super.run_phase(phase);
      forever begin
        sb_fifo.get(seq_item);
        ref_model(seq_item);
        if (seq_item.dout !== dout_ref) begin
          `uvm_error("run_phase", $sformatf("Comparison failed: %s, dout_ref = %0d",
                                            seq_item.convert2string(), dout_ref))
          error_count++;
        end else begin
          `uvm_info("run_phase", $sformatf("Comparison succeeded: %s", seq_item.convert2string()),
                    UVM_HIGH)
          correct_count++;
        end
      end
    endtask  //

    virtual task ref_model(ram_seq_item seq_item_chk);
      if (!seq_item.rst_n) begin
        dout_ref = 0;
        addr = 0;
      end else begin
        if (rx_valid_delayed) begin
          case (din_delayed[9:8])
            2'b01:   ram[addr] = din_delayed[7:0];
            2'b11:   dout_ref = ram[addr];
            default: addr = din_delayed[7:0];
          endcase
        end
      end
      din_delayed = seq_item_chk.din;
      rx_valid_delayed = seq_item_chk.rx_valid;
    endtask  //

    virtual function void report_phase(uvm_phase phase);
      super.report_phase(phase);
      `uvm_info("report phase", $sformatf("Total successful transactions: %0d", correct_count),
                UVM_MEDIUM)
      `uvm_info("report phase", $sformatf("Total failed transactions: %0d", error_count),
                UVM_MEDIUM)
    endfunction
  endclass  //ram_scoreboard extends uvm_scoreboard
endpackage
