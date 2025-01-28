module fifo_with_params_sva
  #(
    parameter FIFO_DEPTH = 8,
    parameter FIFO_WIDTH = 11,
    parameter NUM_LOOPS  = 3,
    parameter logic ADD_MODE   = 1
    )
   (input                             clk ,
    input                         rstn ,
    input                         push ,
    input [FIFO_WIDTH-1:0]        push_data ,
    input                         pop ,
    output logic [FIFO_WIDTH-1:0] pop_data ,
    output logic                  empty ,
    output logic                  full 
    );

   // helper logic for data coloring
   
   logic [FIFO_WIDTH -1:0]        in_data; // driven data into the fifo
   logic [FIFO_WIDTH -1:0]        expected_data; // the colored data expected from the DUT

   logic [NUM_LOOPS-1:0]          shift_pop; // a shifter for the pop signals, used for the manipulation of the colored data
   
   always @(posedge clk or negedge rstn)
     if (!rstn) 
       begin
          in_data <= 'b0;
          expected_data <= 'b0;
       end
     else
       begin
          if (!full && push)
            in_data <= in_data + 1; // colored data increments by 1
          if (!empty && pop)
            expected_data <= expected_data +1; // colored data increments by 1
       end // else: !if(!rstn)

   // shift the pop signal
   always @(posedge clk or negedge rstn)
     if (!rstn) 
       shift_pop <= 'b0;
     else
       shift_pop <= {shift_pop,pop};

   
   default clocking dc @(posedge clk); endclocking
   default disable iff (!rstn);

   // fifo assumes
   ASM_underflow: assume property (empty |-> !pop);
   ASM_overflow: assume property (full |-> !push);

   // data coloring assumes
   ASM_input: assume property (!full && push |-> (push_data == in_data));

   // output asserts

   generate
      begin: mode_ast
         if (ADD_MODE)
           begin
              AST_output_add: assert property (shift_pop[NUM_LOOPS-1] |-> (pop_data == 
                                                                               FIFO_WIDTH'(expected_data - $countones(shift_pop)+NUM_LOOPS)));
           end
         else
           begin
              AST_output_sub: assert property (shift_pop[NUM_LOOPS-1]
                                                   |-> (pop_data == 
                                                        FIFO_WIDTH'(expected_data - $countones(shift_pop)-NUM_LOOPS)));
           end // else: !if(ADD_MODE)
      end // block: mode_ast
   endgenerate

   

   /////// DUT inst ///////
   fifo_with_params#(
                     .FIFO_DEPTH (FIFO_DEPTH),
                     .FIFO_WIDTH (FIFO_WIDTH),
                     .NUM_LOOPS(NUM_LOOPS),
                     .ADD_MODE(ADD_MODE)
                     )
   u_dut
     (.*);




endmodule
