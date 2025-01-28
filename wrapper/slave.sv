import slave_shared_pkg::*;

module SPI_Slave (
    MOSI,
    MISO,
    SS_n,
    SCK,
    rst_n,
    rx_data,
    tx_data,
    rx_valid,
    tx_valid
);

  input MOSI, SS_n;
  input SCK, rst_n;
  output reg MISO;

  input [7:0] tx_data;
  input tx_valid;
  output reg [9:0] rx_data;
  output reg rx_valid;

  reg [3:0] wr_counter;
  reg [3:0] rd_counter;
  // wire invalid_wr, invalid_rd_addr, invalid_rd_data;

  (* fsm_encoding = "gray"*)
  state_e cs, ns;

  //handle invalid cases
  // assign invalid_wr = (cs == WRITE) && (wr_counter == 7) && (rx_data[9:8] != 2'b00) && (rx_data[9:8] != 2'b01);
  // assign invalid_rd_addr = (cs == READ_ADD) && (wr_counter == 7) && (rx_data[9:8] != 2'b10);
  // assign invalid_rd_data = (cs == READ_DATA) && (wr_counter == 7) && (rx_data[9:8] != 2'b11);

  // next state logic
  always @(*) begin
    case (cs)
      IDLE: begin
        if (~slaveif.SS_n) begin
          ns = CHK_CMD;
        end else begin
          ns = IDLE;
        end
      end
      CHK_CMD: begin
        if (~slaveif.SS_n && MOSI && slaveif.read_addr_received) begin
          ns = READ_DATA;
        end else if (~slaveif.SS_n && MOSI && ~slaveif.read_addr_received) begin
          ns = READ_ADD;
        end else if (~slaveif.SS_n && ~MOSI) begin
          ns = WRITE;
        end else begin
          ns = IDLE;
        end
      end
      WRITE: begin
        if (slaveif.SS_n || wr_counter == 0) begin
          ns = IDLE;
        end else begin
          ns = WRITE;
        end
      end
      READ_ADD: begin
        if (slaveif.SS_n || wr_counter == 0) begin
          ns = IDLE;
        end else begin
          ns = READ_ADD;
        end
      end
      READ_DATA: begin
        if (slaveif.SS_n || rd_counter == 0) begin
          ns = IDLE;
        end else begin
          ns = READ_DATA;
        end
      end
      default: ns = IDLE;
    endcase
  end

  // state memory 
  always @(posedge SCK or negedge rst_n) begin
    if (~rst_n) begin
      cs <= IDLE;
    end else begin
      cs <= ns;
    end
  end

  // output logic
  always @(posedge SCK or negedge rst_n) begin
    if (~rst_n) begin
      wr_counter <= 9;
      rd_counter <= 7;
      rx_data <= 0;
      slaveif.read_addr_received <= 0;
      MISO <= 0;
      rx_valid <= 0;
    end else begin
      case (cs)
        IDLE: begin
          wr_counter <= 9;
          rd_counter <= 7;
          rx_data <= 0;
          rx_valid <= 0;
          MISO <= 0;
        end
        WRITE: begin
          // drive rx_data bus with parallel write address / data
          rx_data[wr_counter] <= MOSI;
          wr_counter <= (wr_counter > 0) ? wr_counter - 1 : 0;
          // check data is valid or not
          rx_valid <= (wr_counter == 0) ? 1 : 0;
        end
        READ_ADD: begin
          // drive rx_data bus with parallel read address
          rx_data[wr_counter] <= MOSI;
          wr_counter <= (wr_counter > 0) ? wr_counter - 1 : 0;
          // check data is valid or not
          rx_valid <= (wr_counter == 0) ? 1 : 0;
          // indicate address is received
          slaveif.read_addr_received <= (wr_counter == 0) ? 1 : 0;
        end
        READ_DATA: begin

          // check data is valid or not
          rx_valid <= 0;
          if (wr_counter != 4'he) begin
            // drive rx_data bus with parallel read command & dummy data
            rx_data[wr_counter] <= MOSI;
            wr_counter <= wr_counter - 1;

          end else if (slaveif.tx_valid) begin
            // receive parallel data and convert it to serial on MISO port
            MISO <= slaveif.tx_data[rd_counter];
            rd_counter <= rd_counter - 1;
            if (rd_counter == 1) begin
              // indicate received address is used and waiting for new address
              slaveif.read_addr_received <= 0;
            end
          end
        end
      endcase
    end
  end

endmodule
