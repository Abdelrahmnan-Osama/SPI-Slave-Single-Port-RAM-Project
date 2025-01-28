import uvm_pkg::*;
import wrapper_test_pkg::*;
`include "uvm_macros.svh"

module top ();
  bit clk;

  initial begin
    forever begin
      #1 clk = ~clk;
    end
  end

  wrapper_if wif (clk);
  ram_if ramif (wif.clk);
  slave_if slaveif (wif.clk);

  SPI_wrapper DUT (wif);

  bind DUT.ram ram_sva ram_sva_inst (
      ramif.clk,
      ramif.din,
      ramif.rst_n,
      ramif.rx_valid,
      ramif.dout,
      ramif.rx_valid
  );
  bind DUT.slave slave_sva slave_sva_inst (
      slaveif.SCK,
      slaveif.rst_n,
      slaveif.SS_n,
      slaveif.MOSI,
      slaveif.tx_data,
      slaveif.tx_valid,
      slaveif.MISO,
      slaveif.rx_data,
      slaveif.rx_valid
  );

  assign ramif.din = DUT.rx_data;
  assign ramif.rst_n = wif.rst_n;
  assign ramif.rx_valid = DUT.rx_valid;
  assign ramif.dout = DUT.tx_data;
  assign ramif.tx_valid = DUT.tx_valid;

  assign slaveif.rst_n = wif.rst_n;
  assign slaveif.SS_n = wif.SS_n;
  assign slaveif.MOSI = wif.MOSI;
  assign slaveif.tx_data = DUT.tx_data;
  assign slaveif.tx_valid = DUT.tx_valid;
  assign slaveif.MISO = wif.MISO;
  assign slaveif.rx_data = DUT.rx_data;
  assign slaveif.rx_valid = DUT.rx_valid;


  initial begin
    uvm_config_db#(virtual wrapper_if)::set(null, "uvm_test_top", "wrapper_IF", wif);
    uvm_config_db#(virtual slave_if)::set(null, "uvm_test_top", "slave_IF", slaveif);
    uvm_config_db#(virtual ram_if)::set(null, "uvm_test_top", "RAM_IF", ramif);
    run_test("wrapper_test");
  end
endmodule
