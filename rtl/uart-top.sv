`default_nettype none

/**
 * Top level uart module without any FIFO buffering
 **/
module uart
  (
    // Generic
    input  logic       uart_clk,
                       core_clk,
                       uart_rst_n,
                       core_rst_n,
    // External interface
    input  logic       rx_datastream,
    output logic       tx_datastream,
    // Host transmit interface
    input  logic       tx_data_valid,
    input  logic [7:0] tx_data,
    output logic       tx_data_ready,
    // Host receive interface
    input  logic       rx_data_ready,
    input  logic       rx_framing_err_clr,
    output logic       rx_data_valid,
    output logic [7:0] rx_data,
    output logic       rx_overrun,
    output logic       rx_framing_err
  );

  logic [7:0] rx_data_unbuf, tx_data_unbuf;
  logic       rx_buf_ready, rx_data_unbuf_valid,
              rx_buf_data_invalid, rx_buf_not_ready,
              tx_buf_not_ready, tx_buf_data_invalid,
              tx_buf_data_valid, tx_data_unbuf_ready;

  receiver uart_recv(.clk(uart_clk),
                     .rst_n(uart_rst_n),
                     .raw_rx_bitstream(rx_datastream),
                     .host_ready(rx_buf_ready),
                     .clear_framing_err(rx_framing_err_clr),
                     .rx_data(rx_data_unbuf),
                     .rx_data_valid(rx_data_unbuf_valid),
                     .framing_err(rx_framing_err),
                     .overrun(rx_overrun));



  transmitter uart_write(.clk(uart_clk),
                         .rst_n(uart_rst_n),
                         .tx_data_valid(tx_buf_data_valid),
                         .tx_data(tx_data_unbuf),
                         .tx_data_ready(tx_data_unbuf_ready),
                         .tx_serial_out(tx_datastream));

  async_fifo #(.DSIZE(8), .ASIZE(3)) uart_rx_fifo(.winc(rx_data_unbuf_valid),
                                                  .wclk(uart_clk),
                                                  .wrst_n(uart_rst_n),
                                                  .rinc(rx_data_ready),
                                                  .rclk(core_clk),
                                                  .rrst_n(core_rst_n),
                                                  .wdata(rx_data_unbuf),
                                                  .rdata(rx_data),
                                                  .wfull(rx_buf_not_ready),
                                                  .rempty(rx_buf_data_invalid));

  async_fifo #(.DSIZE(8), .ASIZE(3)) uart_tx_fifo(.winc(tx_data_valid),
                                                  .wclk(core_clk),
                                                  .wrst_n(core_rst_n),
                                                  .rinc(tx_data_unbuf_ready),
                                                  .rclk(uart_clk),
                                                  .rrst_n(uart_rst_n),
                                                  .wdata(tx_data),
                                                  .rdata(tx_data_unbuf),
                                                  .wfull(tx_buf_not_ready),
                                                  .rempty(tx_buf_data_invalid));
  // rx_data is valid if rx buffer data is valid
  assign rx_data_valid = ~rx_buf_data_invalid;
  assign rx_buf_ready = ~rx_buf_not_ready;
  assign tx_buf_data_valid = ~tx_buf_data_invalid;


  assign tx_data_ready = ~tx_buf_not_ready;

endmodule: uart
