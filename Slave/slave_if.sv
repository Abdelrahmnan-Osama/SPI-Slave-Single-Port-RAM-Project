interface slave_if (
    SCK
);
  input bit SCK;

  logic MOSI, SS_n;
  logic rst_n;
  logic MISO;

  logic [7:0] tx_data;
  logic tx_valid;
  logic [9:0] rx_data;
  logic rx_valid;
  logic read_addr_received;

  modport DUT (
  input SCK, rst_n, SS_n, MOSI, tx_data, tx_valid, read_addr_received,
  output MISO, rx_data, rx_valid
  );
endinterface  //slave_if()
