module slave_sva (
    slave_if.DUT slaveif
);

  property p_slave_not_selected;
    @(posedge slaveif.SCK) disable iff (!slaveif.rst_n) slaveif.SS_n |=> ##1 !slaveif.rx_valid;
  endproperty

  property p_read_operation;
    @(posedge slaveif.SCK) disable iff (!slaveif.rst_n) $fell(
        slaveif.SS_n
    ) ##1 (slaveif.read_addr_received throughout slaveif.MOSI [* 3]) |=> !slaveif.rx_valid [* 9];
  endproperty

  property p_write_addr;
    @(posedge slaveif.SCK) disable iff (!slaveif.rst_n || slaveif.SS_n) $fell(
        slaveif.SS_n
    ) ##1 !slaveif.MOSI [* 3] |=> !slaveif.rx_valid ##1 !slaveif.rx_valid [* 7] ##1 $rose(
        slaveif.rx_valid
    ) ##1 $fell(
        slaveif.rx_valid
    );
  endproperty

  property p_read_addr;
    @(posedge slaveif.SCK) disable iff (!slaveif.rst_n || slaveif.SS_n) $fell(
        slaveif.SS_n
    ) ##1 (!slaveif.read_addr_received throughout slaveif.MOSI [* 2] ##1 !slaveif.MOSI) |=>
        !slaveif.rx_valid ##1 !slaveif.rx_valid [* 7] ##1 $rose(
        slaveif.rx_valid
    ) ##1 $fell(
        slaveif.rx_valid
    );
  endproperty

  property p_write_data;
    @(posedge slaveif.SCK) disable iff (!slaveif.rst_n || slaveif.SS_n) $fell(
        slaveif.SS_n
    ) ##1 !slaveif.MOSI [* 2] ##1 slaveif.MOSI |=>
        !slaveif.rx_valid ##1 !slaveif.rx_valid [* 7] ##1 $rose(
        slaveif.rx_valid
    ) ##1 $fell(
        slaveif.rx_valid
    );
  endproperty

  // property p_read_addr;
  //   @(posedge slaveif.SCK) disable iff (!slaveif.rst_n) $fell(
  //       slaveif.SS_n
  //   ) ##1 slaveif.MOSI [* 2] ##1 !slaveif.MOSI |=> !slaveif.rx_valid [* 7] ##1 $rose(
  //       slaveif.rx_valid
  //   ) ##1 $fell(
  //       slaveif.rx_valid
  //   );
  // endproperty



  slave_not_selected_assertion :
  assert property (p_slave_not_selected);
  slave_not_selected_coverage :
  cover property (p_slave_not_selected);

  read_operation_assertion :
  assert property (p_read_operation);
  read_operation_coverage :
  cover property (p_read_operation);

  write_addr_assertion :
  assert property (p_write_addr);
  write_addr_coverage :
  cover property (p_write_addr);

  read_addr_assertion :
  assert property (p_read_addr);
  read_addr_coverage :
  cover property (p_read_addr);

  write_data_assertion :
  assert property (p_write_data);
  write_data_coverage :
  cover property (p_write_data);

  always_comb begin
    if (!slaveif.rst_n) begin
      reset_assertion : assert final (slaveif.rx_valid === 0);
    end

  end
endmodule
