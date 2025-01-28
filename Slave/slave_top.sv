import uvm_pkg::*;
import slave_test_pkg::*;
`include "uvm_macros.svh"

module top ();
  bit clk;

  initial begin
    forever begin
      #1 clk = ~clk;
    end
  end

  slave_if slaveif (clk);
  SPI_Slave DUT (slaveif);
  bind SPI_Slave slave_sva slave_sva_inst (slaveif);

  initial begin
    uvm_config_db#(virtual slave_if)::set(null, "uvm_test_top", "slave_IF", slaveif);
    run_test("slave_test");
  end
endmodule
