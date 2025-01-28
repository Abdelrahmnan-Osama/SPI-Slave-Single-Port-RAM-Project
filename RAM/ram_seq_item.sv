package ram_seq_item_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  class ram_seq_item extends uvm_sequence_item;
    `uvm_object_utils(ram_seq_item)

    rand bit [9:0] din;
    rand bit rst_n, rx_valid;
    logic [7:0] dout;
    logic tx_valid;

    function new(string name = "ram_seq_item");
      super.new(name);
    endfunction  //new()

    virtual function string convert2string();
      return $sformatf(
          "%s rst_n = %b, rx_valid = %b, din = %0d, tx_valid = %b, dout = %0d",
          super.convert2string(),
          rst_n,
          rx_valid,
          din,
          tx_valid,
          dout
      );
    endfunction

    virtual function string convert2string_stimulus();
      return $sformatf("rst_n = %b, rx_valid = %b, din = %0d", rst_n, rx_valid, din);
    endfunction

    constraint reset_c {
      soft rst_n dist {
        0 := 2,
        1 := 98
      };
    }

    constraint rx_valid_c {
      rx_valid dist {
        0 := 30,
        1 := 70
      };
    }

    constraint din_c {
      soft din[9:8] dist {
        2'b00 := 25,
        2'b01 := 25,
        2'b10 := 25,
        2'b11 := 25
      };
    }

  endclass  //ram_seq_item extends uvm_seq_item
endpackage

