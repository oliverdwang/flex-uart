`default_nettype none

`define NUM_DATA_BITS 8
`define MIN_BIT_LEN 14
`define SPEC_BIT_LEN 16
`define MAX_BIT_LEN 18

`define NUM_TRIALS 100
`define TIMEOUT_LEN 24

class uartPkt;
  rand bit [7:0] data;
  bit [4:0] dataLen [`NUM_DATA_BITS];

  rand bit [4:0] startLen;
  rand bit [4:0] data0Len;
  rand bit [4:0] data1Len;
  rand bit [4:0] data2Len;
  rand bit [4:0] data3Len;
  rand bit [4:0] data4Len;
  rand bit [4:0] data5Len;
  rand bit [4:0] data6Len;
  rand bit [4:0] data7Len;
  rand bit [4:0] stopLen;

  constraint startBit {startLen inside {[`MIN_BIT_LEN:`MAX_BIT_LEN]};}
  constraint data0Bit {data0Len inside {[`MIN_BIT_LEN:`MAX_BIT_LEN]};}
  constraint data1Bit {data1Len inside {[`MIN_BIT_LEN:`MAX_BIT_LEN]};}
  constraint data2Bit {data2Len inside {[`MIN_BIT_LEN:`MAX_BIT_LEN]};}
  constraint data3Bit {data3Len inside {[`MIN_BIT_LEN:`MAX_BIT_LEN]};}
  constraint data4Bit {data4Len inside {[`MIN_BIT_LEN:`MAX_BIT_LEN]};}
  constraint data5Bit {data5Len inside {[`MIN_BIT_LEN:`MAX_BIT_LEN]};}
  constraint data6Bit {data6Len inside {[`MIN_BIT_LEN:`MAX_BIT_LEN]};}
  constraint data7Bit {data7Len inside {[`MIN_BIT_LEN:`MAX_BIT_LEN]};}

  function new();
    dataLen[0] = data0Len;
    dataLen[1] = data1Len;
    dataLen[2] = data2Len;
    dataLen[3] = data3Len;
    dataLen[4] = data4Len;
    dataLen[5] = data5Len;
    dataLen[6] = data6Len;
    dataLen[7] = data7Len;
  endfunction: new

endclass: uartPkt


module top();
  // DUT interface
  // Generic
  logic clk, rst_n;
  // External
  logic tb_tx, tb_rx;
  // Host tx interface
  logic tx_data_valid, tx_data_ready;
  logic [7:0] tx_data;
  // Host rx interface
  logic rx_data_valid, rx_data_ready;
  logic [7:0] rx_data;

  uart dut(.clk,
           .rst_n,
           .rx_datastream(tb_tx),
           .tx_datastream(tb_rx),
           .tx_data_valid,
           .tx_data_ready,
           .tx_data,
           .rx_data_valid,
           .rx_data_ready,
           .rx_data);


  uartPkt packet = new;

  // Clock generator
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // Test suite
  initial begin
    // Receive packets with host interface ready
    nominal_uart_rx_test();

    @(posedge clk);

    // Send packets from the host interface
    nominal_uart_tx_test();

    // Wrap up test after small delay
    end_simulation();
  end

  /***************************************************************************/
  /* TEST HELPERS                                                            */
  /***************************************************************************/

  task reset_context;
    rst_n <= 1'b1;

    tb_tx <= 1'b1;
    tx_data_valid <= 1'b0;
    tx_data <= 8'd0;
    rx_data_ready <= 1'b0;
    @(posedge clk);

    rst_n <= 1'b0;
    @(posedge clk);

    rst_n <= 1'b1;
    @(posedge clk);
  endtask

  task end_simulation;
    for (int i = 0; i < `TIMEOUT_LEN; i++) begin
      @(posedge clk);
    end

    $finish;
  endtask

  /**
   * Task to simplify simulating a packet being sent from an external device
   * to the UART module and receiving it on the host interface
   */
  task tb_send_packet;
    if (!packet.randomize())
      $warning("Error with randomizing UART packet");

    // Send start bit
    tb_tx <= 1'b0;
    for (int i = 0; i < packet.startLen; i++) begin
      @(posedge clk);
    end

    // Send all data bits
    for (int i = 0; i < `NUM_DATA_BITS; i++) begin
      tb_tx <= packet.data[i];
      for (int j = 0; j < packet.dataLen[i]; j++) begin
        @(posedge clk);
      end
    end

    // Send stop bit
    tb_tx <= 1'b1;
    for (int i = 0; i < packet.stopLen; i++) begin
      @(posedge clk);
    end
  endtask

  /**
   * Task to simplify simulating a packet being sent from the host interface to
   * an external device through the UART module
   */
  task tb_receive_packet;
    if (!packet.randomize())
      $warning("Error with randomizing UART packet");

    // Wait for transmit interface to free up
    while (!tx_data_ready) begin
      @(posedge clk);
    end

    // Simulate host sending data
    tx_data <= packet.data;
    tx_data_valid <= 1'b1;
    @(posedge clk);
    while (!tx_data_ready) begin
      @(posedge clk);
    end
    // at this point, tx_data_ready and tx_data_valid should be asserted
    // transfer is about to occur, deassert valid next cycle
    // Finish host handshaking session
    tx_data_valid <= 1'b0;
    @(posedge clk);

    // for (int i = 0; tx_data_ready; i++) begin
    //   assert (i < `TIMEOUT_LEN)
    //     else $error("tx_data_ready not unset after tx_data_valid for %i clk edges", `TIMEOUT_LEN);

    //   @(posedge clk);
    // end

  endtask

  /**
    * Task to wait for the inputs to propagate through the bit synchronizer
    * takes 3 cycles
    */
  task wait_for_bit_synchronizer;
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);
  endtask

  /***************************************************************************/
  /* WRITTEN TESTS                                                           */
  /***************************************************************************/

  task nominal_uart_rx_test;
    for(int i = 0; i < `NUM_TRIALS; i++) begin
      reset_context();

      tb_send_packet();
      wait_for_bit_synchronizer();

      assert (rx_data_valid)
        else $error("rx_data_valid not set after proper UART packet received");
      assert (rx_data == packet.data)
        else $error("Data received (%h) does not match sent data (%h)", rx_data, packet.data);
      // Check that data was receieved properly
      // let's handshake to the UART that we are ready to latch in data
      rx_data_ready <= 1'b1;
      @(posedge clk);
      while (!rx_data_valid) begin
        @(posedge clk);
      end
      // at this point, we know rx_data_read & rx_data_valid
      // transfer will occur
      rx_data_ready <= 1'b0;
      @(posedge clk);

      // TODO: this is not technically true valid/ready requirement
      assert (!rx_data_valid)
        else $error("rx_data_valid still set after acknowledgement with unsetting rx_data_ready");
    end
  endtask

  task nominal_uart_tx_test;
    for (int i = 0; i < `NUM_TRIALS; i++) begin
      reset_context();
      tb_receive_packet();

      // Wait for start bit to appear on tb_rx
      while (tb_rx == 1'b1) begin
        @(posedge clk);
      end

      // Check that start bit was transmitted properly
      for (int j = 0; j < `SPEC_BIT_LEN; j++) begin
        assert (tb_rx == 1'b0)
          else $error("Start bit (%i) was not low", tb_rx);
      end

      // Check that all data bits were transmitted properly
      for (int j = 0; j < `NUM_DATA_BITS; j++) begin
        for (int k = 0; k < `SPEC_BIT_LEN; k++) begin
          assert (tb_rx == packet.data[j])
            else $error("Data bit (%i) was not transmitted properly", tb_rx);
        end
      end

      // Check that stop bit was transmitted properly
      for (int j = 0; j < `SPEC_BIT_LEN; j++) begin
        assert (tb_rx == 1'b1)
          else $error("Stop bit (%i) was not transmitted properly", tb_rx);
      end
    end
  endtask

  /***************************************************************************/
  /* PROPERTY ASSERTIONS                                                     */
  /***************************************************************************/

  property drivenOutput (bus);
    @(posedge clk) disable iff (!rst_n)
      (!$isunknown(bus));
  endproperty

  assert property(drivenOutput(tb_rx)) else
    $warning("tx_datastream is X");
  assert property(drivenOutput(tx_data_ready)) else
    $warning("tx_datastream is X");
  assert property(drivenOutput(rx_data_valid)) else
    $warning("rx_data_valid is X");
  assert property(drivenOutput(rx_data)) else
    $warning("rx_data is X");

endmodule: top
