`default_nettype none

module bit_synchronizer
  #(parameter NUM_STAGES = 3)
  (
    input  logic clk,
    input  logic rst_n,
    input  logic data_in,
    output logic data_out
  );

  // MSB is oldest value, LSB is newest value
  logic [NUM_STAGES-1:0] buffer_chain;

  always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
      buffer_chain <= 0;
    end else begin
      buffer_chain <= {buffer_chain[NUM_STAGES-2:0], data_in};
    end
  end

  assign data_out = buffer_chain[NUM_STAGES-1];

endmodule: bit_synchronizer