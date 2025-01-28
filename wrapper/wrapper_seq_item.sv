package wrapper_seq_item_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  class wrapper_seq_item extends uvm_sequence_item;
    `uvm_object_utils(wrapper_seq_item)

    rand bit MOSI, SS_n;
    rand bit rst_n;
    logic MISO;

    // bit mosi_seq[$];

    function new(string name = "wrapper_seq_item");
      super.new(name);
    endfunction  //new()

    virtual function string convert2string();
      return $sformatf(
          "%s rst_n = %b, SS_n = %b, MOSI = %b, MISO = %b",
          super.convert2string(),
          rst_n,
          SS_n,
          MOSI,
          MISO
      );
    endfunction

    virtual function string convert2string_stimulus();
      return $sformatf("%s rst_n = %b, SS_n = %b, MOSI = %b", super.convert2string(), rst_n, SS_n,
                       MOSI);
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

  endclass  //wrapper_seq_item extends uvm_seq_item
endpackage

