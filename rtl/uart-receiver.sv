`default_nettype none

module receiver
  (
    input  logic clk,
    input  logic rst_n,
    input  logic raw_rx_bitstream,
  );

  // Synchronize rx bitstream to eliminate metastability
  logic rx_bitstream;
  bit_synchronizer rx_sync(
    .clk(clk),
    .rst_n(rst_n),
    .data_in(raw_rx_bitstream),
    .data_out(rx_bitstream)
  );



  

endmodule: receiver


/**
 * @brief Detects bits from an input bitstream with oversampling
 *
 * @param[in]  clk             Peripheral clock
 * @param[in]  rst_n           Synchronous reset
 * @param[in]  bitstream_in    Input bitstream (that is already synchronized)
 * @param[in]  data_out_ready  Flag to indicate that the host is ready to receive data
 * @param[out] data_out        Bit detected from the bitstream
 * @param[out] data_out_valid  Flag to indicate that a new bit has been detected 
 **/
module bit_detector
  (
    // Generic
    input  logic clk,
                 rst_n,
    // Core interface
    input  logic bitstream_in,
    output logic active_rx,
    output logic bit_ready,
    output logic rx_bit,
    output logic framing_err,
    output logic done
  );

  counter #(.WIDTH(4),
            .STEP(4'd1),
            .RESET_VAL(4'd0)) timing_cntr(.clk,
                                       .rst_n,
                                       .load(resync),
                                       .en(incr_samp_cnt),
                                       .D(4'd0),
                                       .Q(timing_offset));

  counter #(.WIDTH(3),
            .STEP(3'd1),
            .RESET_VAL(3'd0)) bit_cntr(.clk,
                                    .rst_n,
                                    .load(1'b0),
                                    .en(bit_ready),
                                    .D(3'd0),
                                    .Q(bit_count));


  logic last_logic_level, resync;

  /***************************************************************************/
  /* Control FSM                                                             */
  /***************************************************************************/
  enum {
    IDLE,
    START_DETECT,
    RX_SAMPLING,
    STOP_DETECT
  } cs, ns;

  // State update
  always_ff @(posedge clk) begin
    if (~rst_n) begin
      cs <= IDLE;
    end else begin
      cs <= ns;
    end
  end

  // Next state logic
  always_comb begin
    case(cs)
      // wait for a possible start bit
      IDLE: ns = (~bitstream_in) ? START_DETECT : IDLE;
      START_DETECT: begin
        if (timing_offset != 4'd15) begin
          // gotta sample enough times first to see
          ns = START_DETECT;
        end
        else if (~rx_bit) begin
          // the voltage was low when it was sampled, it's a valid start bit
          ns = RX_SAMPLING;
        end
        else
          // the voltage was high when it was sampled, go back to idle
          ns = IDLE;
      end
      RX_SAMPLING: begin
        if ((bit_count == 3'd7) && (timing_offset == 4'd15)) begin
          // last sample of last bit collected, prepare to move for stop bit
          ns = STOP_DETECT;
        end
        else begin
          // not done sampling all data bits
          ns = RX_SAMPLING;
        end
      end
      STOP_DETECT: begin
        ns = (timing_offset == 4'd15) ? IDLE : STOP_DETECT;
      end
    endcase
  end

  // Output logic
  always_comb begin
    active_rx = 1'b0;
    framing_err = 1'b0;
    done = 1'b0;
    take_sample = 1'b0;
    case(cs)
      IDLE: // no outputs necessary
      // take sample at the middle of the cycle
      START_DETECT: take_sample = (timing_offset == 4'd7) ? 1'b1 : 1'b0;
      RX_SAMPLING: begin
        active_rx = 1'b1;
        take_sample = (timing_offset == 4'd7) ? 1'b1 : 1'b0;
      end
      STOP_DETECT: begin
        active_rx = 1'b1;
        take_sample = (timing_offset == 4'd7) ? 1'b1 : 1'b0;
        done = (timing_offset == 4'd15) ? 1'b1 : 1'b0;
        framing_err = (~rx_bit && timing_offset == 4'd15) ? 1'b1 : 1'b0;
      end
    endcase
  end

  // sampling register
  always_ff @(posedge clk) begin
    if (~rst_n) begin
      rx_bit <= 1'b0;
    else begin
      if (take_sample) begin
        rx_bit <= bitstream_in;
      end
    end
  end

  // edge history register (for realignment)
  always_ff @(posedge clk) begin
    if (~rst_n) begin
      last_logic_level <= 1'b0;
    end
    else begin
      last_logic_level <= rx_bitstream;
    end
  end

  // logic for determining final 
  always_comb begin
    bit_ready = 1'b0;
    if (cs == RX_SAMPLING) begin
      if (timing_offset == 4'd15) begin
        bit_ready = 1'b1;
      end
    end
  end

  // when we detect an edge, resync the timing register
  assign resync = (rx_bitstream != last_logic_level) ? 1'b1 : 1'b0;


endmodule: bit_detector