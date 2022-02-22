`default_nettype none

// Number of samples (out of 16) in start bit that need to be low for a valid start bit to be registered
`define LOW_SAMP_IN_START_THRES (8)

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
                 data_out_ready,
    output logic data_out,
                 data_out_valid,
    // Settings
    input  logic oversample_x16
  );

  logic       incr_samp_cnt, clr_samp_cnt
  logic [7:0] sample_count, low_start_cnt;
  counter #(.WIDTH(8),
            .STEP(1),
            .RESET_VAL(0)) samp_cntr(.clk,
                                     .rst_n,
                                     .load(clr_samp_cnt),
                                     .en(incr_samp_cnt),
                                     .D(8'd0),
                                     .Q(sample_count)),
                           low_start_cntr(.clk,
                                          .rst_n,
                                          .load(clr_samp_cnt),
                                          .en(~bitstream_in),
                                          .D(8'd0),
                                          .Q(low_start_cnt));

  /***************************************************************************/
  /* Control FSM                                                             */
  /***************************************************************************/
  enum logic [1:0] {IDLE, READ_START, READ_PACKET} cs, ns;

  // State update
  always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
      cs <= IDLE;
    end else begin
      cs <= ns;
    end
  end

  // Next state and output logic
  always_comb begin
    incr_samp_cnt = 0;
    clr_samp_cnt = 0;

    unique case (cs)
      IDLE: begin
        if (bitstream_in == 0) begin
          ns = READ_START;
          
          incr_samp_cnt = 1;
        end else begin
          ns = IDLE;
          
          clr_samp_cnt = 1;
        end
      end

      READ_START: begin
        if (sample_count < 8'd15) begin
          ns = READ_START;
        end else begin
          if (low_start_cnt < 8'd7) begin
            ns = IDLE;
          end else begin
            ns = READ_PACKET;
          end
        end
        end
      end


    endcase
  end

endmodule: bit_detector