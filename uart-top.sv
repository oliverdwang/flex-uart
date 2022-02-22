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
    output logic       rx_data_valid,
    output logic [7:0] rx_data,
  );

  
  

endmodule: uart