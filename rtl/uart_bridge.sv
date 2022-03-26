`default_nettype none


module uart_bridge
  (
    input  logic CLOCK_50,
	 input  logic [3:0] KEY,
	 input  logic [17:0] SW,
	 input  logic UART_RXD,
	 output logic UART_TXD,
	 output logic [7:0] LEDG
	
  );

  logic clk, rst_n, uart_rx_data_valid, uart_tx_data_ready;
  logic [7:0] uart_rx_data;
  logic [3:0] key_sync, key_final;

  // insert PLL, running at 115200 * 16
  pll myPLL(.areset(SW[0]), .inclk0(CLOCK_50), .c0(clk));
  
  always_ff @(posedge clk) begin
    key_sync <= ~KEY;
	 key_final <= key_sync;
  end
  
  
  assign rst_n = ~key_final[0];
  
  uart DUT(.clk,
           .rst_n,
           .rx_datastream(UART_RXD),
           .tx_datastream(UART_TXD),
           .tx_data_valid(uart_rx_data_valid),
           .tx_data(uart_rx_data),
           .tx_data_ready(uart_tx_data_ready),
           .rx_data_ready(uart_tx_data_ready),
           .rx_framing_err_clr(key_final[1]),
           .rx_data_valid(uart_rx_data_valid),
           .rx_data(uart_rx_data),
           .rx_overrun(LEDG[0]),
           .rx_framing_err(LEDG[1]));
  assign LEDG[7:2] = 6'd0;

endmodule: uart_bridge