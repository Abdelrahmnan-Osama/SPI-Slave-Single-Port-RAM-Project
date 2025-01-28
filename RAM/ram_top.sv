import uvm_pkg::*;
import ram_test_pkg::*;
`include "uvm_macros.svh"

module top ();
  bit clk;

  initial begin
    forever begin
      #1 clk = ~clk;
    end
  end

  ram_if ramif (clk);
  RAM DUT (ramif);
  bind RAM ram_sva ram_sva_inst (ramif);

  initial begin
    uvm_config_db#(virtual ram_if)::set(null, "uvm_test_top", "RAM_IF", ramif);
    run_test("ram_test");
  end
endmodule
