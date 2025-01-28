`define SIM
module RAM (
    ram_if.DUT ramif
);

  parameter ADDR_SIZE = 8;
  logic [ADDR_SIZE-1:0] addr;

  parameter MEM_DEPTH = 256;
  reg [7:0] mem[MEM_DEPTH-1:0];

  // memory read and write operations
  always @(posedge ramif.clk or negedge ramif.rst_n) begin
    if (~ramif.rst_n) begin
      ramif.dout <= 0;
      addr <= 0;
      ramif.tx_valid <= 0;
    end else begin
      case ({
        ramif.din[9:8], ramif.rx_valid
      })
        3'b001: begin
          addr <= ramif.din[7:0];
          ramif.tx_valid <= 0;
        end
        3'b011: begin
          mem[addr] <= ramif.din[7:0];
          ramif.tx_valid <= 0;
        end
        3'b101: begin
          addr <= ramif.din[7:0];
          ramif.tx_valid <= 0;
        end
        3'b111: begin
          ramif.dout <= mem[addr];
          ramif.tx_valid <= 1;
        end
        default: begin
          ramif.tx_valid <= 0;
        end
      endcase
    end
  end

`ifdef SIM
  property p_addr_updated;
    @(posedge ramif.clk) disable iff (!ramif.rst_n) ramif.rx_valid && (ramif.din[9:8] == 2'b00 || ramif.din[9:8] == 2'b10) |=> addr == $past(
        ramif.din[7:0]
    );
  endproperty

  property p_addr_unchanged;
    @(posedge ramif.clk) disable iff (!ramif.rst_n) ramif.rx_valid && (ramif.din[9:8] == 2'b01 || ramif.din[9:8] == 2'b11) |=> addr == $past(
        addr
    );
  endproperty

  address_updated_assertion :
  assert property (p_addr_updated);
  address_updated_coverage :
  cover property (p_addr_updated);

  address_unchanged_assertion :
  assert property (p_addr_unchanged);
  address_unchanged_coverage :
  cover property (p_addr_unchanged);
`endif

endmodule

