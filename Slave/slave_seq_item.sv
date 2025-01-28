package slave_seq_item_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  class slave_seq_item extends uvm_sequence_item;
    `uvm_object_utils(slave_seq_item)

    rand bit MOSI, SS_n;
    rand bit rst_n;
    logic MISO;

    rand bit [7:0] tx_data;
    rand bit tx_valid;
    logic [9:0] rx_data;
    logic rx_valid;

    bit mosi_seq[$];

    function new(string name = "slave_seq_item");
      super.new(name);
    endfunction  //new()

    virtual function string convert2string();
      return $sformatf(
          "%s rst_n = %b, SS_n = %b, MOSI = %b, tx_data = %h, tx_valid = %b, rx_valid = %b, MISO = %b, rx_data = %h",
          super.convert2string(),
          rst_n,
          SS_n,
          MOSI,
          tx_data,
          tx_valid,
          rx_valid,
          MISO,
          rx_data
      );
    endfunction

    virtual function string convert2string_stimulus();
      return $sformatf(
          "%s rst_n = %b, SS_n = %b, MOSI = %b, tx_data = %h, tx_valid = %b",
          super.convert2string(),
          rst_n,
          SS_n,
          MOSI,
          tx_data,
          tx_valid
      );
    endfunction

    constraint reset_c {
      soft rst_n dist {
        0 := 2,
        1 := 98
      };
    }

    constraint slave_select_c {
      //   if (mosi_seq.size() == 11) {
      //     SS_n == 1;
      //   }

      soft SS_n dist {
        1 := 2,
        0 := 98
      };
    }

    // constraint tx_valid_c {
    //   if (mosi_seq.size() == 11 && mosi_seq[0] == 1'b1) {
    //     // check 2nd bit
    //     if (mosi_seq[1] == 1'b1) {
    //       // check 3rd bit
    //       if (mosi_seq[2] == 1'b1) {
    //         // assert tx_valid
    //         tx_valid == 1;
    //       }
    //     }
    //   }
    // }

    constraint tx_valid_c {
      tx_valid dist {
        0 := 70,
        1 := 30
      };
    }



    // constraint MOSI_c {
    //   if (!SS_n && rst_n) {
    //     // first bit can be 0 or 1
    //     if (mosi_seq.size() == 0) {
    //       MOSI inside {1'b0, 1'b1};
    //       // second bit depends on the first 1
    //     } else
    //     if (mosi_seq.size() == 1) {
    //       //write operation
    //       if (mosi_seq[0] == 1'b0) {
    //         MOSI == 1'b0;
    //         // read operation
    //       } else {
    //         MOSI == 1'b1;
    //       }
    //       // perform operation or store address
    //     } else {
    //       MOSI inside {1'b0, 1'b1};
    //     }
    //   }

    // }

    // function post_ramdomize();
    //   if (mosi_seq.size() == 11 || !rst_n || SS_n) begin
    //     mosi_seq.delete();
    //   end else begin
    //     mosi_seq.push_back(MOSI);
    //   end
    // endfunction



  endclass  //slave_seq_item extends uvm_seq_item
endpackage

