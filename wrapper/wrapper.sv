module SPI_wrapper (
    wrapper_if.DUT wif
);

  wire [9:0] rx_data;
  wire [7:0] tx_data;
  wire rx_valid, tx_valid;

  SPI_Slave slave (
      .MOSI(slaveif.MOSI),
      .MISO(wif.MISO),
      .SS_n(slaveif.SS_n),
      .SCK(slaveif.SCK),
      .rst_n(slaveif.rst_n),
      .rx_data(rx_data),
      .tx_data(tx_data),
      .rx_valid(rx_valid),
      .tx_valid(tx_valid)
  );

  RAM ram (
      .din(rx_data),
      .rx_valid(rx_valid),
      .dout(tx_data),
      .tx_valid(tx_valid),
      .clk(ramif.clk),
      .rst_n(ramif.rst_n)
  );

endmodule
