package ram_seq_pkg;
  import uvm_pkg::*;
  import ram_seq_item_pkg::*;
  `include "uvm_macros.svh"

  class ram_reset_seq extends uvm_sequence #(ram_seq_item);
    `uvm_object_utils(ram_reset_seq)

    ram_seq_item seq_item;

    function new(string name = "ram_reset_seq");
      super.new(name);
    endfunction  //new()

    virtual task body();
      seq_item = ram_seq_item::type_id::create("seq_item");
      start_item(seq_item);
      rst_rand : assert (seq_item.randomize() with {rst_n == 0;});
      finish_item(seq_item);
    endtask
  endclass  //ram_reset_seq extends uvm_sequence #(ram_seq_item)

  class ram_main_seq extends uvm_sequence #(ram_seq_item);
    `uvm_object_utils(ram_main_seq)

    ram_seq_item seq_item;

    function new(string name = "ram_main_seq");
      super.new(name);
    endfunction  //new()

    virtual task body();
      repeat (10000) begin
        seq_item = ram_seq_item::type_id::create("seq_item");
        start_item(seq_item);
        main_seq : assert (seq_item.randomize());
        finish_item(seq_item);
      end

    endtask
  endclass  //ram_main_seq extends uvm_sequence #(ram_seq_item)

endpackage
