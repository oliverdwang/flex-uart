`default_nettype none

`define NUM_DATA_BITS 8
`define MIN_BIT_LEN 14
`define SPEC_BIT_LEN 16
`define MAX_BIT_LEN 18

`define NUM_TRIALS 100
`define TIMEOUT_LEN 24

class uartPkt;
  rand bit [7:0] data;
  rand bit [4:0] dataLen [`NUM_DATA_BITS];

  rand bit [4:0] startLen;
  rand bit [4:0] stopLen;

  constraint startBit {startLen inside {[`MIN_BIT_LEN:`MAX_BIT_LEN]};}
  constraint dataBitLen { foreach (dataLen[i]) {
      dataLen[i] inside {[`MIN_BIT_LEN:`MAX_BIT_LEN]};
    }
  }
  constraint stopBit {stopLen inside {[`MIN_BIT_LEN:`MAX_BIT_LEN]};}

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
  logic rx_framing_err, rx_framing_err_clr, rx_overrun;

  uart dut(.clk,
           .rst_n,
           .rx_datastream(tb_tx),
           .tx_datastream(tb_rx),
           .tx_data_valid,
           .tx_data_ready,
           .tx_data,
           .rx_data_valid,
           .rx_data_ready,
           .rx_data,
           .rx_framing_err,
           .rx_framing_err_clr,
           .rx_overrun);


  uartPkt packet = new;
  logic [7:0] temp;

  // Clock generator
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // Test suite
  initial begin
    // Receive packets with host interface ready
    // nominal_uart_rx_test();

    // uart_basic_rx_overrun_test();

    // uart_rx_overrun_reset_test();

    // uart_rx_basic_framing_test();

    // uart_rx_framing_reset_test();

    uart_send_random_shit_test();

    @(posedge clk);
    end_simulation();
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
    rx_framing_err_clr <= 1'b0;

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

  task generate_packet;
    int cur_bit;
    int prev_bit;
    int sum = 0;
    int done = 0;
    int num_bits = 1;
    while (!done) begin
      if (!packet.randomize()) begin
        $warning("Error with generating random UART packet");
        done = 1;
      end
      else begin
        int violated = 0;
        for (int i = 0; i < `NUM_DATA_BITS + 1; i++) begin
          if (i == 0) begin
            cur_bit = 0;
            prev_bit = cur_bit;
          end
          else begin
            cur_bit = packet.data[i-1];
            if (cur_bit == prev_bit) begin
              sum += packet.dataLen[i-1];
              num_bits++;
            end
            else begin
              sum = packet.dataLen[i-1];
              num_bits = 1;
            end
            if (num_bits * `SPEC_BIT_LEN > sum) begin
              if (num_bits * `SPEC_BIT_LEN - sum >= `SPEC_BIT_LEN/2) begin
                violated = 1;
                break;
              end
            end
            else begin
              if (sum - num_bits * `SPEC_BIT_LEN >= `SPEC_BIT_LEN/2) begin
                violated = 1;
                $display("violated, restarting, num_bits (%d), total len: (%d)", num_bits, sum);
                $display("packet was (%b)", packet.data);
                $display("i was (%d)", i);
                break;
              end
            end
            prev_bit = cur_bit;
          end
        end
        if (!violated) begin
          done = 1;
        end
      end
    end
  endtask

  /**
   * Task to simplify simulating a packet being sent from an external device
   * to the UART module and receiving it on the host interface
   */
  task tb_send_packet;
    generate_packet();

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
   * Task to simplify simulating a packet being sent that contains
   * an obvious framing error by not having a stop bit sent correctly
   */
  task tb_send_packet_bad_frame;
    generate_packet();

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

    // Send no stop bit
    tb_tx <= 1'b0;
    for (int i = 0; i < packet.stopLen; i++) begin
      @(posedge clk);
    end
    // reset to high
    tb_tx <= 1'b1;
  endtask
  

  /**
   * Task to simplify simulating a packet being sent from the host interface to
   * an external device through the UART module
   */
  task tb_receive_packet;
    generate_packet();

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

  task uart_send_random_shit_test;
    int num_bits;
    int bitLen[];
    int inBits[];
    for (int i = 0; i < `NUM_TRIALS; i++) begin
      reset_context();
      num_bits = $urandom_range(256,16); // generate 16-256 bits
      bitLen = new [num_bits];
      inBits = new [num_bits];
      for (int j = 0; j < num_bits; j++) begin
        bitLen[j] = $urandom_range(64,5); // and each bit held for between 5 and 64 edges for funsies
        inBits[j] = $urandom_range(1,0); // generate 1s and 0s
      end 
      
      for (int j = 0; j < num_bits; j++) begin
        tb_tx <= inBits[j];
        for (int k = 0; k < bitLen[j]; k++) begin
          @(posedge clk);
        end
      end // send random crap


      tb_tx <= 1'b1; // reset it to high line
      @(posedge clk);

      if (rx_data_valid) begin
        // read and clear the errors, put it into a known state
        rx_data_ready <= 1'b1;
        rx_framing_err_clr <= 1'b1;
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);
        rx_data_ready <= 1'b0;
        rx_framing_err_clr <= 1'b0;
        @(posedge clk);
      end

      tb_send_packet();
      wait_for_bit_synchronizer();
	
      assert (rx_data_valid)
        else begin
          $display("startLen: (%d), stopLen: (%d), data: (%b)", packet.startLen, packet.stopLen, packet.data);
          for (int i = 0; i < `NUM_DATA_BITS; i++) begin
            $display("bit (%d) duration: (%d)", i, packet.dataLen[i]);
          end
          $error("rx_data_valid not set after proper UART packet received");
        end
      assert (rx_data == packet.data)
        else begin
          $display("startLen: (%d), stopLen: (%d), data: (%b)", packet.startLen, packet.stopLen, packet.data);
          for (int i = 0; i < `NUM_DATA_BITS; i++) begin
            $display("bit (%d) duration: (%d)", i, packet.dataLen[i]);
          end
          $error("Data received (%h) does not match sent data (%h)", rx_data, packet.data);
        end
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
        else $error("rx_data_valid still set after acknowledgement with rx_data_ready");



    end

  endtask

  task nominal_uart_rx_test;
    for(int i = 0; i < `NUM_TRIALS; i++) begin
      reset_context();

      tb_send_packet();
      wait_for_bit_synchronizer();
	
      assert (rx_data_valid)
        else begin
          $display("startLen: (%d), stopLen: (%d), data: (%b)", packet.startLen, packet.stopLen, packet.data);
          for (int i = 0; i < `NUM_DATA_BITS; i++) begin
            $display("bit (%d) duration: (%d)", i, packet.dataLen[i]);
          end
          $error("rx_data_valid not set after proper UART packet received");
        end
      assert (rx_data == packet.data)
        else begin
          $display("startLen: (%d), stopLen: (%d), data: (%b)", packet.startLen, packet.stopLen, packet.data);
          for (int i = 0; i < `NUM_DATA_BITS; i++) begin
            $display("bit (%d) duration: (%d)", i, packet.dataLen[i]);
          end
          $error("Data received (%h) does not match sent data (%h)", rx_data, packet.data);
        end
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
        else $error("rx_data_valid still set after acknowledgement with rx_data_ready");
    end
  endtask

  task uart_basic_rx_overrun_test;
    for (int i = 0; i < `NUM_TRIALS; i++) begin
      reset_context();
      tb_send_packet();
      wait_for_bit_synchronizer();
      assert (rx_data_valid)
        else begin
          $display("startLen: (%d), stopLen: (%d), data: (%b)", packet.startLen, packet.stopLen, packet.data);
          for (int i = 0; i < `NUM_DATA_BITS; i++) begin
            $display("bit (%d) duration: (%d)", i, packet.dataLen[i]);
          end
          $error("rx_data_valid not set after proper UART packet received");
        end
      assert (rx_data == packet.data)
        else begin
          $display("startLen: (%d), stopLen: (%d), data: (%b)", packet.startLen, packet.stopLen, packet.data);
          for (int i = 0; i < `NUM_DATA_BITS; i++) begin
            $display("bit (%d) duration: (%d)", i, packet.dataLen[i]);
          end
          $error("Data received (%h) does not match sent data (%h)", rx_data, packet.data);
        end
      temp <= packet.data;
      @(posedge clk);
      tb_send_packet();
      wait_for_bit_synchronizer();
      assert (rx_data_valid)
        else begin
          $display("startLen: (%d), stopLen: (%d), data: (%b)", packet.startLen, packet.stopLen, packet.data);
          for (int i = 0; i < `NUM_DATA_BITS; i++) begin
            $display("bit (%d) duration: (%d)", i, packet.dataLen[i]);
          end
          $error("rx_data_valid not set after proper UART packet received");
        end
      assert (rx_data == temp)
        else begin
          $error("Data received (%h) changed even though we didn't read from it. Original: (%h)", rx_data, temp);
        end

      tb_send_packet();
      wait_for_bit_synchronizer();
      assert (rx_data_valid)
        else begin
          $display("startLen: (%d), stopLen: (%d), data: (%b)", packet.startLen, packet.stopLen, packet.data);
          for (int i = 0; i < `NUM_DATA_BITS; i++) begin
            $display("bit (%d) duration: (%d)", i, packet.dataLen[i]);
          end
          $error("rx_data_valid not set after proper UART packet received");
        end
      assert (rx_data == temp)
        else begin
          $error("Data received (%h) changed even though we didn't read from it. Original: (%h)", rx_data, temp);
        end
      assert (rx_overrun)
        else begin
          $error("Overrun not set despite buffers being overrun");
        end
    end
  endtask


  task uart_rx_overrun_reset_test;
    for (int i = 0; i < `NUM_TRIALS; i++) begin
      reset_context();
      tb_send_packet();
      wait_for_bit_synchronizer();
      assert (rx_data_valid)
        else begin
          $display("startLen: (%d), stopLen: (%d), data: (%b)", packet.startLen, packet.stopLen, packet.data);
          for (int i = 0; i < `NUM_DATA_BITS; i++) begin
            $display("bit (%d) duration: (%d)", i, packet.dataLen[i]);
          end
          $error("rx_data_valid not set after proper UART packet received");
        end
      assert (rx_data == packet.data)
        else begin
          $display("startLen: (%d), stopLen: (%d), data: (%b)", packet.startLen, packet.stopLen, packet.data);
          for (int i = 0; i < `NUM_DATA_BITS; i++) begin
            $display("bit (%d) duration: (%d)", i, packet.dataLen[i]);
          end
          $error("Data received (%h) does not match sent data (%h)", rx_data, packet.data);
        end
      temp <= packet.data;
      @(posedge clk);

      tb_send_packet();
      wait_for_bit_synchronizer();
      assert (rx_data_valid)
        else begin
          $display("startLen: (%d), stopLen: (%d), data: (%b)", packet.startLen, packet.stopLen, packet.data);
          for (int i = 0; i < `NUM_DATA_BITS; i++) begin
            $display("bit (%d) duration: (%d)", i, packet.dataLen[i]);
          end
          $error("rx_data_valid not set after proper UART packet received");
        end
      assert (rx_data == temp)
        else begin
          $error("Data received (%h) changed even though we didn't read from it. Original: (%h)", rx_data, temp);
        end

      tb_send_packet();
      wait_for_bit_synchronizer();
      assert (rx_data_valid)
        else begin
          $display("startLen: (%d), stopLen: (%d), data: (%b)", packet.startLen, packet.stopLen, packet.data);
          for (int i = 0; i < `NUM_DATA_BITS; i++) begin
            $display("bit (%d) duration: (%d)", i, packet.dataLen[i]);
          end
          $error("rx_data_valid not set after proper UART packet received");
        end
      assert (rx_data == temp)
        else begin
          $error("Data received (%h) changed even though we didn't read from it. Original: (%h)", rx_data, temp);
        end
      assert (rx_overrun)
        else begin
          $error("Overrun not set despite buffers being overrun");
        end

            // Check that data was receieved properly
      // let's handshake to the UART that we are ready to latch in data
      rx_data_ready <= 1'b1;
      @(posedge clk);
      while (!rx_data_valid) begin
        @(posedge clk);
      end
      // at this point, we know rx_data_read & rx_data_valid
      // transfer will occur
      @(posedge clk);

      assert (~rx_overrun)
        else begin
          $error("overrun not cleared after reading");
        end

      // TODO: this is not technically true valid/ready requirement
      assert (!rx_data_valid)
        else begin
          $error("rx_data_valid still set after acknowledgement with rx_data_ready");
        end

      @(posedge clk);

      assert (rx_data_valid)
        else begin
          $error("rx_data_valid not set even though buffer should contain valid data");
        end
      
      assert (~rx_overrun)
        else begin
          $error("overrun erroneously set after unloading 1 buffer");
        end
    end
  endtask

  task uart_rx_basic_framing_test;
    reset_context();
    tb_send_packet_bad_frame();
    wait_for_bit_synchronizer();
    assert (rx_data_valid)
      else begin
        $error("push out data as best effort, but we didn't signal valid");
      end
    assert (rx_framing_err)
      else begin
        $error("framing error should have been asserted but was not");
      end
  endtask

  task uart_rx_framing_reset_test;
    reset_context();
    tb_send_packet_bad_frame();
    wait_for_bit_synchronizer();
    assert (rx_data_valid)
      else begin
        $error("push out data as best effort, but we didn't signal valid");
      end
    assert (rx_framing_err)
      else begin
        $error("framing error should have been asserted but was not");
      end
    rx_framing_err_clr <= 1'b1;
    @(posedge clk);
    rx_framing_err_clr <= 1'b0;
    @(posedge clk);

    assert (~rx_framing_err)
      else begin
        $error("framing error should have been cleared but was not");
      end
    
    tb_send_packet_bad_frame();
    wait_for_bit_synchronizer();
    assert (rx_data_valid)
      else begin
        $error("push out data as best effort, but we didn't signal valid");
      end
    assert (rx_framing_err)
      else begin
        $error("framing error should have been asserted but was not");
      end
    // send a normal packet now, framing err should still be set from previous bad txn
    tb_send_packet();
    wait_for_bit_synchronizer();
    assert (rx_data_valid)
      else begin
        $display("startLen: (%d), stopLen: (%d), data: (%b)", packet.startLen, packet.stopLen, packet.data);
        for (int i = 0; i < `NUM_DATA_BITS; i++) begin
          $display("bit (%d) duration: (%d)", i, packet.dataLen[i]);
        end
        $error("rx_data_valid not set after proper UART packet received");
      end
    assert (rx_framing_err)
      else begin
        $error("framing error should've persisted but didn't");
      end
    rx_framing_err_clr <= 1'b1;
    @(posedge clk);
    @(posedge clk);

    assert (~rx_framing_err)
      else begin
        $error("framing error should have been cleared but was not");
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
