`default_nettype none

/**
 * Top level uart module without any FIFO buffering
 **/
module uart
  (
    // Generic
    input  logic       clk,
                       rst_n,
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

  receiver uart_recv(.clk,
                     .rst_n,
                     .raw_rx_bitstream(rx_datastream),
                     .host_ready(rx_data_ready),
                     .clear_framing_err(rx_framing_err_clr),
                     .rx_data,
                     .rx_data_valid,
                     .framing_err(rx_framing_err),
                     .overrun(rx_overrun));

  transmitter uart_write(.clk,
                         .rst_n,
                         .tx_data_valid,
                         .tx_data,
                         .tx_data_ready,
                         .tx_serial_out(tx_datastream));
  

endmodule: uart