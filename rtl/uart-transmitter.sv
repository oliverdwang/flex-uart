`default_nettype none


/** 
 * @brief Does an 8N1 UART transmission using ready/valid signals
 *
 *
 * @param[in]  clk            Peripheral clock
 * @param[in]  rst_n          Synchronous reset
 * @param[in]  tx_data_valid  Flag that indicates when tx_data has valid data on the line
 * @param[in]  tx_data        Input transmission data, 1 byte
 * @param[out] tx_data_ready  Flag that indicates when the transmitter is able to receive one more byte to send
 * @param[out] tx_serial_out  Serial output from transmitter, HI when inactive, tx_data stream when active
 **/
module transmitter
  (
    // Generic
    input  logic       clk,
    input  logic       rst_n,
    // Host transmit interface
    input  logic       tx_data_valid,
    input  logic [7:0] tx_data,  
    // External interface
    output logic       tx_data_ready,
    output logic       tx_serial_out
  );

  logic [7:0] latched_tx_data;
  logic [3:0] count;
  logic [9:0] shift_out; // to include start and stop bit
  logic latch_data, xfer_to_shift, do_tx, do_shift;

  /***************************************************************************/
  /* Control FSM                                                             */
  /***************************************************************************/
  enum {
    IDLE,
    STAGE,
    TRANSMIT_BUF_EMPTY,
    TRANSMIT_BUF_FULL
  } ns, cs;

  // State update
  always_ff @(posedge clk) begin
    if (~rst_n) begin
      cs <= IDLE;
    end
    else begin
      cs <= ns;
    end
  end

  // Next state logic
  always_comb begin
    case(cs)
      IDLE: ns = (tx_data_valid) ? STAGE : IDLE;
      STAGE: ns = (tx_data_valid) ? TRANSMIT_BUF_FULL : TRANSMIT_BUF_EMPTY;
      TRANSMIT_BUF_EMPTY: begin
        if (~last_bit_tx & ~tx_data_valid) begin
          ns = TRANSMIT_BUF_EMPTY;
        end 
        else if (~last_bit_tx & tx_data_valid) begin
          ns = TRANSMIT_BUF_FULL;
        end
        else if (last_bit_tx & ~tx_data_valid) begin
          ns = IDLE; 
        end
        else begin
          ns = STAGE;
        end
      end
      TRANSMIT_BUF_FULL: ns = (last_bit_tx) ? STAGE : TRANSMIT_BUF_FULL;
    endcase
  end

  // Output logic
  always_comb begin
    tx_data_ready = 1'b0;
    latch_data = 1'b0;
    xfer_to_shift = 1'b0;
    do_tx = 1'b0;
    case(cs)
      IDLE: begin
        tx_data_ready = 1'b1;        
        if (ns == STAGE) begin
          latch_data = 1'b1;
        end
      end
      STAGE: begin
        tx_data_ready = 1'b1;
        xfer_to_shift = 1'b1;
      end
      TRANSMIT_BUF_EMPTY: begin
        do_tx = 1'b1;
        tx_data_ready = 1'b1;
      end
      TRANSMIT_BUF_FULL: begin
        do_tx = 1'b1;
      end
    endcase
  end

  // transmit buffer and shift register
  always_ff @(posedge clk) begin
    if (~rst_n) begin
      latched_tx_data <= 'd0;
      shift_out <= 'd0;
    end
    else begin
      if (latch_data) begin
        latched_tx_data <= tx_data;
      end

      if (xfer_to_shift) begin
        // data sent LSB first, stop and start it encoded in shift register
        shift_out <= {1'b1, latched_tx_data, 1'b0};
      end else if (do_shift) begin
        shift_out <= {1'b0, shift_out[9:1]};
      end
    end
  end

  // tie to HI until it's time to transmit
  assign tx_serial_out = (cs == TRANSMIT_BUF_EMPTY || cs == TRANSMIT_BUF_FULL) ? shift_out[0] : 1'b1;

  // logic to control when to shift the register
  bit_shifter shift_ctrl(
    .clk,
    .rst_n,
    .do_tx,
    .last_bit_tx,
    .do_shift
  );


endmodule: transmitter


/**
 * @brief Handles when to shift the output register by counting clock edges
 *
 * @param[in]  clk          Peripheral clock
 * @param[in]  rst_n        Synchronous reset
 * @param[in]  do_tx        Input asserted when the transmitter is in active transmission state
 * @param[out] last_bit_tx  Flag asserted when on the last clock cycle of the last bit to transmit
 * @param[out] do_shift     Flag asserted when the shift register should shift to next bit
 **/
module bit_shifter
  (
    // Generic
    input  logic clk,
    input  logic rst_n,

    // Interface
    input  logic do_tx,
    output logic last_bit_tx,
    output logic do_shift
  );

  logic [3:0] clk_cnt, bits_sent;

  // clock divider
  counter #(WIDTH=4) xmit_divider(.clk, .rst_n, .load(1'b0), .en(do_tx), .D(4'd0), .Q(clk_cnt));
  // track how many bits we've sent
  counter #(WIDTH=4) shifted_counter(.clk, .rst_n, .load(clear_bit_cnt), .en(do_shift), .D(4'd0), .Q(bits_sent));
  
  always_comb begin
    do_shift = 1'b0;
    last_bit_tx = 1'b0;
    clear_bit_cnt = 1'b0;

    // since the clock runs at 16x for oversampling
    if (do_tx && clk_cnt == 4'd15) begin
      do_shift = 1'b1;
    end

    // we're on the last bit and the last clock cycle
    if (do_tx && bits_sent == 4'd9 && clk_cnt == 4'd15) begin
      last_bit_tx = 1'b1;
      clear_bit_cnt = 1'b1;
    end
  end

endmodule: bit_shifter