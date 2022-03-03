`default_nettype none

module receiver
  (
    input  logic       clk,
    input  logic       rst_n,
    input  logic       raw_rx_bitstream,
    input  logic       host_ready,
    input  logic       clear_framing_err,
    output logic [7:0] rx_data,
    output logic       rx_data_valid,
    output logic       framing_err,
    output logic       overrun
  );

  // Synchronize rx bitstream to eliminate metastability
  logic rx_bitstream, active_rx, bit_ready, rx_bit, done, framing_err_internal;
  bit_synchronizer #(.RESET_VAL(3'b111)) rx_sync(
    .clk(clk),
    .rst_n(rst_n),
    .data_in(raw_rx_bitstream),
    .data_out(rx_bitstream)
  );

  logic [7:0] shift_in;
  logic xfer_to_buf;

  bit_detector rx_core(.clk,
                       .rst_n,
                       .bitstream_in(rx_bitstream),
                       .active_rx,
                       .bit_ready,
                       .rx_bit,
                       .framing_err(framing_err_internal),
                       .done);

  enum {
    IDLE_BUF_EMPTY,
    RX_IN_PROG,
    IDLE_BUF_FULL,
    RX_IN_PROG_FULL,
    FULL,
    FULL_OVERRUN,
    UNLOAD_BUF,
    UNLOAD_BUF_FULL
  } cs, ns;

  // state register
  always_ff @(posedge clk) begin
    if (~rst_n) begin
      cs <= IDLE_BUF_EMPTY;
    end
    else begin
      cs <= ns;
    end
  end

  // next state logic
  always_comb begin
    ns = IDLE_BUF_EMPTY;
    case(cs)
      IDLE_BUF_EMPTY: ns = (active_rx) ? RX_IN_PROG : IDLE_BUF_EMPTY;
      RX_IN_PROG: ns = (done) ? IDLE_BUF_FULL : RX_IN_PROG;
      IDLE_BUF_FULL: begin
        if (host_ready & ~active_rx) begin
          ns = IDLE_BUF_EMPTY;
        end
        else if (host_ready & active_rx) begin
          ns = RX_IN_PROG;
        end
        else if (~host_ready & active_rx) begin
          ns = RX_IN_PROG_FULL;
        end
        else begin
          ns = IDLE_BUF_FULL;
        end
      end
      RX_IN_PROG_FULL: begin
        if (host_ready & ~done) begin
          ns = RX_IN_PROG;
        end
        else if (host_ready & done) begin
          ns = UNLOAD_BUF;
        end
        else if (~host_ready & done) begin
          ns = FULL;
        end
        else begin
          ns = RX_IN_PROG_FULL;
        end
      end
      FULL: begin
        if (~host_ready & bit_ready) begin // give more leeway, no overrun until there's a bit we can't take in
          ns = FULL_OVERRUN;
        end
        else if (~host_ready & ~bit_ready) begin
          ns = FULL;
        end
        else if (host_ready & bit_ready) begin
          ns = UNLOAD_BUF_FULL;
        end
        else begin
          ns = IDLE_BUF_FULL;
        end
      end
      FULL_OVERRUN: begin
        ns = (host_ready) ? UNLOAD_BUF_FULL : FULL_OVERRUN;
      end
      UNLOAD_BUF: begin
        ns = IDLE_BUF_FULL;
      end
      UNLOAD_BUF_FULL: begin
        // if we're in the middle of a dropped packet, just wait until it's done
        // before letting host know we're ready to give more data
        ns = (active_rx) ? UNLOAD_BUF_FULL : IDLE_BUF_FULL;
      end
      default: begin
        ns = IDLE_BUF_EMPTY;
      end 
    endcase
  end

  // output logic
  always_comb begin
    xfer_to_buf = 1'b0;
    rx_data_valid = 1'b0;
    overrun = 1'b0;

    case(cs)
      IDLE_BUF_EMPTY: begin
        // no outputs here
      end
      RX_IN_PROG: xfer_to_buf = (ns == IDLE_BUF_FULL) ? 1'b1 : 1'b0;
      IDLE_BUF_FULL: rx_data_valid = 1'b1;
      RX_IN_PROG_FULL: rx_data_valid = 1'b1;
      FULL: begin
        rx_data_valid = 1'b1;
        if (host_ready & ~bit_ready) begin
          xfer_to_buf = 1'b1;
        end
      end
      FULL_OVERRUN: begin
        overrun = 1'b1;
        rx_data_valid = 1'b1;
      end
      UNLOAD_BUF: xfer_to_buf = 1'b1;
      UNLOAD_BUF_FULL: xfer_to_buf = (active_rx) ? 1'b0 : 1'b1;
      default: begin
      end
    endcase
  end

  // shift & data registers
  always_ff @(posedge clk) begin
    if (~rst_n) begin
      framing_err <= 1'b0;
      shift_in <= 8'd0;
      rx_data <= 8'd0;
    end
    else begin
      if (bit_ready) begin
        shift_in <= {rx_bit, shift_in[7:1]};
      end


      if (xfer_to_buf) begin  
        rx_data <= {rx_bit, shift_in[7:1]};
      end


      if (framing_err_internal) begin
        framing_err <= 1'b1;
      end
      else if (clear_framing_err) begin
        framing_err <= 1'b0;
      end


    end
  end

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

  logic [3:0] timing_offset;
  logic [2:0] bit_count;
  logic last_logic_level, resync, take_sample, do_edge_count;

  counter #(.WIDTH(4),
            .STEP(4'd1),
            .RESET_VAL(4'd0)) timing_cntr(.clk,
                                       .rst_n,
                                       .load(resync),
                                       .en(do_edge_count),
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
        if ((bit_count == 3'd7) && (timing_offset == 4'd8)) begin
          // last sample of last bit collected, prepare to move for stop bit
          ns = STOP_DETECT;
        end
        else begin
          // not done sampling all data bits
          ns = RX_SAMPLING;
        end
      end
      STOP_DETECT: begin
        ns = (timing_offset == 4'd8) ? IDLE : STOP_DETECT;
      end
      default: ns = IDLE;
    endcase
  end

  // Output logic
  always_comb begin
    active_rx = 1'b0;
    framing_err = 1'b0;
    done = 1'b0;
    take_sample = 1'b0;
    do_edge_count = 1'b1;
    case(cs)
      IDLE: begin
        if (ns == START_DETECT) begin
          do_edge_count = 1'b0; // don't count time in IDLE
        end
      end
      // take sample at the middle of the cycle
      START_DETECT: take_sample = (timing_offset == 4'd7) ? 1'b1 : 1'b0;
      RX_SAMPLING: begin
        active_rx = 1'b1;
        take_sample = (timing_offset == 4'd7) ? 1'b1 : 1'b0;
      end
      STOP_DETECT: begin
        active_rx = 1'b1;
        take_sample = (timing_offset == 4'd7) ? 1'b1 : 1'b0;
        done = (timing_offset == 4'd8) ? 1'b1 : 1'b0;
        framing_err = (~rx_bit && timing_offset == 4'd8) ? 1'b1 : 1'b0;
      end
    endcase
  end

  // sampling register
  always_ff @(posedge clk) begin
    if (~rst_n) begin
      rx_bit <= 1'b0;
    end
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
      last_logic_level <= bitstream_in;
    end
  end

  // logic for determining final 
  always_comb begin
    bit_ready = 1'b0;
    if (cs == RX_SAMPLING) begin
      if (timing_offset == 4'd8) begin
        bit_ready = 1'b1;
      end
    end
  end

  // when we detect an edge, resync the timing register
  assign resync = ((bitstream_in != last_logic_level) && (timing_offset == 4'd1 || timing_offset == 4'd14)) ? 1'b1 : 1'b0;


endmodule: bit_detector
