import slave_shared_pkg::*;

module SPI_Slave (
    slave_if.DUT slaveif
);

  reg [3:0] wr_counter;
  reg [3:0] rd_counter;
  // wire invalid_wr, invalid_rd_addr, invalid_rd_data;

  (* fsm_encoding = "gray"*)
  state_e cs, ns;

  //handle invalid cases
  // assign invalid_wr = (cs == WRITE) && (wr_counter == 7) && (slaveif.rx_data[9:8] != 2'b00) && (slaveif.rx_data[9:8] != 2'b01);
  // assign invalid_rd_addr = (cs == READ_ADD) && (wr_counter == 7) && (slaveif.rx_data[9:8] != 2'b10);
  // assign invalid_rd_data = (cs == READ_DATA) && (wr_counter == 7) && (slaveif.rx_data[9:8] != 2'b11);

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
        if (~slaveif.SS_n && slaveif.MOSI && slaveif.read_addr_received) begin
          ns = READ_DATA;
        end else if (~slaveif.SS_n && slaveif.MOSI && ~slaveif.read_addr_received) begin
          ns = READ_ADD;
        end else if (~slaveif.SS_n && ~slaveif.MOSI) begin
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
  always @(posedge slaveif.SCK or negedge slaveif.rst_n) begin
    if (~slaveif.rst_n) begin
      cs <= IDLE;
    end else begin
      cs <= ns;
    end
  end

  // output logic
  always @(posedge slaveif.SCK or negedge slaveif.rst_n) begin
    if (~slaveif.rst_n) begin
      wr_counter <= 9;
      rd_counter <= 7;
      slaveif.rx_data <= 0;
      slaveif.read_addr_received <= 0;
      slaveif.MISO <= 0;
      slaveif.rx_valid <= 0;
    end else begin
      case (cs)
        IDLE: begin
          wr_counter <= 9;
          rd_counter <= 7;
          slaveif.rx_data <= 0;
          slaveif.rx_valid <= 0;
          slaveif.MISO <= 0;
        end
        WRITE: begin
          // drive slaveif.rx_data bus with parallel write address / data
          slaveif.rx_data[wr_counter] <= slaveif.MOSI;
          wr_counter <= (wr_counter > 0) ? wr_counter - 1 : 0;
          // check data is valid or not
          slaveif.rx_valid <= (wr_counter == 0) ? 1 : 0;
        end
        READ_ADD: begin
          // drive slaveif.rx_data bus with parallel read address
          slaveif.rx_data[wr_counter] <= slaveif.MOSI;
          wr_counter <= (wr_counter > 0) ? wr_counter - 1 : 0;
          // check data is valid or not
          slaveif.rx_valid <= (wr_counter == 0) ? 1 : 0;
          // indicate address is received
          slaveif.read_addr_received <= (wr_counter == 0) ? 1 : 0;
        end
        READ_DATA: begin

          // check data is valid or not
          slaveif.rx_valid <= 0;
          if (wr_counter != 4'he) begin
            // drive slaveif.rx_data bus with parallel read command & dummy data
            slaveif.rx_data[wr_counter] <= slaveif.MOSI;
            wr_counter <= wr_counter - 1;

          end else if (slaveif.tx_valid) begin
            // receive parallel data and convert it to serial on slaveif.MISO port
            slaveif.MISO <= slaveif.tx_data[rd_counter];
            rd_counter   <= rd_counter - 1;
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
