package slave_seq_pkg;
  import uvm_pkg::*;
  import slave_seq_item_pkg::*;
  `include "uvm_macros.svh"

  class slave_reset_seq extends uvm_sequence #(slave_seq_item);
    `uvm_object_utils(slave_reset_seq)

    slave_seq_item seq_item;

    function new(string name = "slave_reset_seq");
      super.new(name);
    endfunction  //new()

    virtual task body();
      seq_item = slave_seq_item::type_id::create("seq_item");
      start_item(seq_item);
      rst_rand : assert (seq_item.randomize() with {rst_n == 0;});
      finish_item(seq_item);
    endtask
  endclass  //slave_reset_seq extends uvm_sequence #(slave_seq_item)

  class slave_main_seq extends uvm_sequence #(slave_seq_item);
    `uvm_object_utils(slave_main_seq)

    slave_seq_item seq_item;

    function new(string name = "slave_main_seq");
      super.new(name);
    endfunction  //new()

    virtual task body();
      repeat (10000) begin
        seq_item = slave_seq_item::type_id::create("seq_item");
        start_item(seq_item);
        main_seq : assert (seq_item.randomize());
        finish_item(seq_item);
      end

    endtask
  endclass  //slave_main_seq extends uvm_sequence #(slave_seq_item)

endpackage
