`define SIM
module RAM (
    din,
    clk,
    rst_n,
    rx_valid,
    dout,
    tx_valid
);

  input [9:0] din;
  input clk, rst_n, rx_valid;
  output reg [7:0] dout;
  output reg tx_valid;

  parameter ADDR_SIZE = 8;
  logic [ADDR_SIZE-1:0] addr;

  parameter MEM_DEPTH = 256;
  reg [7:0] mem[MEM_DEPTH-1:0];

  // memory read and write operations
  always @(posedge clk or negedge rst_n) begin
    if (~rst_n) begin
      dout <= 0;
      addr <= 0;
      tx_valid <= 0;
    end else begin
      case ({
        din[9:8], rx_valid
      })
        3'b001: begin
          addr <= din[7:0];
          tx_valid <= 0;
        end
        3'b011: begin
          mem[addr] <= din[7:0];
          tx_valid  <= 0;
        end
        3'b101: begin
          addr <= din[7:0];
          tx_valid <= 0;
        end
        3'b111: begin
          dout <= mem[addr];
          tx_valid <= 1;
        end
      endcase
    end
  end

`ifdef SIM
  property p_addr_updated;
    @(posedge clk) disable iff (!rst_n) rx_valid && (din[9:8] == 2'b00 || din[9:8] == 2'b10) |=> addr == $past(
        din[7:0]
    );
  endproperty

  property p_addr_unchanged;
    @(posedge clk) disable iff (!rst_n) rx_valid && (din[9:8] == 2'b01 || din[9:8] == 2'b11) |=> addr == $past(
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

