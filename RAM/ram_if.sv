interface ram_if(clk);
    input bit clk;
    logic [9:0] din;
    logic rst_n, rx_valid;
    logic  [7:0] dout;
    logic  tx_valid;

    modport DUT (
    input clk, din, rst_n, rx_valid,
    output dout, tx_valid
    );
endinterface //ram_if(clk)