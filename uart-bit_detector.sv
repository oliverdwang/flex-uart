`default_nettype none

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



endmodule: bit_detector