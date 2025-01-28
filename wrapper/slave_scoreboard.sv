package slave_scoreboard_pkg;
  import uvm_pkg::*;
  import slave_seq_item_pkg::*;
  `include "uvm_macros.svh"

  class slave_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(slave_scoreboard)

    uvm_analysis_export #(slave_seq_item) sb_export;
    uvm_tlm_analysis_fifo #(slave_seq_item) sb_fifo;
    slave_seq_item seq_item;

    logic MISO_ref;
    logic [9:0] rx_data_ref;
    bit [1:0] start_countdown;
    bit should_read;
    bit addr_received;
    bit SS_n_delayed;
    bit last_read;
    bit [3:0] wr_count, rd_count;


    int correct_count, error_count;

    function new(string name = "slave_scoreboard", uvm_component parent = null);
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
        if (rx_data_ref !== seq_item.rx_data || MISO_ref !== seq_item.MISO) begin
          `uvm_error("run_phase", $sformatf(
                                      "Comparison failed: %s, MISO_ref = %b, rx_data_ref = %h",
                                      seq_item.convert2string(), MISO_ref, rx_data_ref))
          error_count++;
        end else begin
          `uvm_info("run_phase", $sformatf("Comparison succeeded: %s", seq_item.convert2string()),
                    UVM_HIGH)
          correct_count++;
        end
      end
    endtask  //

    virtual task ref_model(slave_seq_item seq_item_chk);
      if (!seq_item_chk.rst_n) begin
        // wait two cycles before sending data
        start_countdown = 2;
        // reset immediately in same cycle
        wr_count = 9;
        rd_count = 7;
        rx_data_ref = 0;
        MISO_ref = 0;
        should_read = 0;
        addr_received = 0;
        last_read = 0;
      end else if (SS_n_delayed) begin
        if (should_read && addr_received && rd_count == 4'hf) begin
          addr_received = 0;
        end
        if (should_read && !addr_received && wr_count == 4'hf) begin
          addr_received = 1;
        end
        // wait just one cycle before sending data
        start_countdown = 1;
        // reset one cycle later
        wr_count = 9;
        rd_count = 7;
        rx_data_ref = 0;
        MISO_ref = 0;
        should_read = 0;
        last_read = 0;
      end else if (start_countdown == 0) begin
        // handle read operation
        // operation is read, dummy data written, and data to be read is ready, then read.
        if (should_read && addr_received && wr_count == 4'he && seq_item_chk.tx_valid && rd_count != 0) begin
          MISO_ref = seq_item_chk.tx_data[rd_count];
          rd_count = rd_count - 1;
          // sequence of data is finished in read operation
          if (rd_count == 0) begin
            last_read = 1;
            addr_received = 0;
          end

          // handle last read operation
        end else if (last_read) begin
          if (seq_item_chk.tx_valid) begin
            MISO_ref = seq_item_chk.tx_data[rd_count];
          end
          rd_count = rd_count - 1;
          if (rd_count == 4'hf) begin
            start_countdown = 1;
          end

          // handle write operation
        end else if (wr_count != 4'he) begin
          rx_data_ref[wr_count] = seq_item_chk.MOSI;
          wr_count = wr_count - 1;
          if (wr_count == 4'he) begin
            if (!should_read || !addr_received) begin
              wr_count = 9;
              rx_data_ref = 0;
              start_countdown = 1;
            end
            if (should_read && !addr_received) begin
              addr_received = 1;
            end
          end
        end

        // automatic reset after complete read-write cycle
      end else if (wr_count == 4'he && rd_count == 4'hf) begin
        wr_count = 9;
        rd_count = 7;
        rx_data_ref = 0;
        MISO_ref = 0;
        should_read = 0;
        last_read = 0;
      end else begin
        // delay before writing data
        start_countdown -= 1;
        if (start_countdown == 0) begin
          should_read = seq_item_chk.MOSI;
        end
      end
      SS_n_delayed = seq_item_chk.SS_n;
    endtask  //

    virtual function void report_phase(uvm_phase phase);
      super.report_phase(phase);
      `uvm_info("report phase", $sformatf("Total successful transactions: %0d", correct_count),
                UVM_MEDIUM)
      `uvm_info("report phase", $sformatf("Total failed transactions: %0d", error_count),
                UVM_MEDIUM)
    endfunction
  endclass  //slave_scoreboard extends uvm_scoreboard
endpackage
