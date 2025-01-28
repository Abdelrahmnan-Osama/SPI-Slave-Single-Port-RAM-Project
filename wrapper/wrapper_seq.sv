package wrapper_seq_pkg;
  import uvm_pkg::*;
  import wrapper_seq_item_pkg::*;
  `include "uvm_macros.svh"

  class wrapper_reset_seq extends uvm_sequence #(wrapper_seq_item);
    `uvm_object_utils(wrapper_reset_seq)

    wrapper_seq_item seq_item;

    function new(string name = "wrapper_reset_seq");
      super.new(name);
    endfunction  //new()

    virtual task body();
      seq_item = wrapper_seq_item::type_id::create("seq_item");
      start_item(seq_item);
      rst_rand : assert (seq_item.randomize() with {rst_n == 0;});
      finish_item(seq_item);
    endtask
  endclass  //wrapper_reset_seq extends uvm_sequence #(wrapper_seq_item)

  class wrapper_main_seq extends uvm_sequence #(wrapper_seq_item);
    `uvm_object_utils(wrapper_main_seq)

    wrapper_seq_item seq_item;

    function new(string name = "wrapper_main_seq");
      super.new(name);
    endfunction  //new()

    virtual task body();
      repeat (10000) begin
        seq_item = wrapper_seq_item::type_id::create("seq_item");
        start_item(seq_item);
        main_seq : assert (seq_item.randomize());
        finish_item(seq_item);
      end

    endtask
  endclass  //wrapper_main_seq extends uvm_sequence #(wrapper_seq_item)

endpackage
