`default_nettype none


module uart_bridge
  (
    /* insert clock, rst_n, LEDs, buttons */
  );

  logic clk, rst_n, uart_rx_data_valid, uart_tx_data_ready;
  logic [7:0] uart_rx_data;

  // insert PLL
  uart DUT(.clk,
           .rst_n,
           .rx_datastream(/* external UART input pin */),
           .tx_data_stream(/* external UART output pin */),
           .tx_data_valid(uart_rx_data_valid),
           .tx_data(uart_rx_data),
           .tx_data_ready(uart_tx_data_ready),
           .rx_data_ready(uart_tx_data_ready),
           .rx_framing_err_clr(/* some button */),
           .rx_data_valid(uart_rx_data_valid),
           .rx_data(uart_rx_data),
           .rx_overrun(/* some LED */),
           .rx_framing_err(/* some LED */));

endmodule: uart_bridge