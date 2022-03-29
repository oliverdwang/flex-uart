`default_nettype none


module uart_bridge
  (
    input  logic CLOCK_50,
	 input  logic [3:0] KEY,
	 input  logic [9:0] SW,
	 inout  logic [35:0] GPIO_1,
	 output logic [9:0] LEDR
	
  );

  logic clk, rst_n, uart_rx_data_valid, uart_tx_data_ready;
  logic [7:0] uart_rx_data;
  logic [3:0] key_sync, key_final;

  // insert PLL, running at 115200 * 16
  pll myPLL(.refclk(CLOCK_50), .rst(SW[0]), .outclk_0(clk), .locked(LEDR[2]));
  
  always_ff @(posedge clk) begin
    key_sync <= ~KEY;
	 key_final <= key_sync;
  end
  
  
  assign rst_n = ~key_final[0];
  
  uart DUT(.clk,
           .rst_n,
           .rx_datastream(GPIO_1[1]),
           .tx_datastream(GPIO_1[35]),
           .tx_data_valid(uart_rx_data_valid),
           .tx_data(uart_rx_data),
           .tx_data_ready(uart_tx_data_ready),
           .rx_data_ready(uart_tx_data_ready),
           .rx_framing_err_clr(key_final[1]),
           .rx_data_valid(uart_rx_data_valid),
           .rx_data(uart_rx_data),
           .rx_overrun(LEDR[0]),
           .rx_framing_err(LEDR[1]));
  assign LEDR[9:4] = 'd0;
  assign LEDR[3] = 1'd1;

endmodule: uart_bridge