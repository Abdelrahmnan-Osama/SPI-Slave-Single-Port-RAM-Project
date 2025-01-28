module ram_sva (
    ram_if.DUT ramif
);

  property p_output_valid;
    @(posedge ramif.clk) disable iff (!ramif.rst_n) ramif.rx_valid && (ramif.din[9:8] == 2'b11) |=> ramif.tx_valid;
  endproperty

  property p_output_invalid;
    @(posedge ramif.clk) disable iff (!ramif.rst_n) !ramif.rx_valid || (ramif.din[9:8] != 2'b11) |=> !ramif.tx_valid;
  endproperty



  output_valid_assertion :
  assert property (p_output_valid);
  output_valid_coverage :
  cover property (p_output_valid);

  output_invalid_assertion :
  assert property (p_output_invalid);
  output_invalid_coverage :
  cover property (p_output_invalid);

  always_comb begin
    if (!ramif.rst_n) begin
      reset_assertion : assert final (ramif.tx_valid === 0);
    end

  end
endmodule
