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


module counter
  #(parameter WIDTH = 8, STEP = 1, RESET_VAL = 0)
  (
    input  logic             clk,
                             rst_n,
                             load,
                             en,
    input  logic [WIDTH-1:0] D,
    output logic [WIDTH-1:0] Q
  );

  always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
      Q <= RESET_VAL;
    end else begin
      if (load) begin
        Q <= D;
      end
      else begin
        Q <= Q + STEP;
      end
    end
  end

endmodule: counter