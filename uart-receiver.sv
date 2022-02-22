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