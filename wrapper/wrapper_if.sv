interface wrapper_if (
    clk
);
  input bit clk;

  logic MOSI, SS_n;
  logic rst_n;
  logic MISO;

  modport DUT (
  input clk, rst_n, SS_n, MOSI,
  output MISO
  );
endinterface  //wrapper_if()
