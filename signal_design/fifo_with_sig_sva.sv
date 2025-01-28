module fifo_with_sig_sva
#(
    parameter max_FIFO_DEPTH = 8,
    parameter max_FIFO_WIDTH = 11,
    parameter max_NUM_LOOPS  = 6,
    parameter logic max_ADD_MODE   = 1
    )
   (
    input                             clk ,
    input                             rstn ,
    input                             push ,
    input [max_FIFO_WIDTH-1:0]        push_data ,
    input                             pop ,
    output logic [max_FIFO_WIDTH-1:0] pop_data ,
    output logic                      empty ,
    output logic                      full ,
    input [3:0]                       sig_FIFO_DEPTH ,
    input [3:0]                       sig_FIFO_WIDTH,
    input [$clog2(max_NUM_LOOPS):0] sig_NUM_LOOPS,
    input sig_ADD_MODE
    );
   
   // stable and range assumes
    ASM_PARAM_FIFO_DEPTH_STABLE: assume property (@(posedge clk) disable iff (!rstn) $stable(sig_FIFO_DEPTH));
    ASM_PARAM_FIFO_DEPTH_RANGE: assume property (@(posedge clk) disable iff (!rstn) sig_FIFO_DEPTH==2 || sig_FIFO_DEPTH==4 || sig_FIFO_DEPTH==8);
    ASM_PARAM_FIFO_WIDTH_STABLE: assume property (@(posedge clk) disable iff (!rstn) $stable(sig_FIFO_WIDTH));
    ASM_PARAM_FIFO_WIDTH_RANGE: assume property (@(posedge clk) disable iff (!rstn) sig_FIFO_WIDTH==8 || sig_FIFO_WIDTH==9 || sig_FIFO_WIDTH==10 || sig_FIFO_WIDTH==11);
    ASM_PARAM_NUM_LOOPS_STABLE: assume property (@(posedge clk) disable iff (!rstn) $stable(sig_NUM_LOOPS));
    ASM_PARAM_NUM_LOOPS_RANGE: assume property (@(posedge clk) disable iff (!rstn) sig_NUM_LOOPS==3 || sig_NUM_LOOPS==4 || sig_NUM_LOOPS==5 || sig_NUM_LOOPS==6);
    ASM_PARAM_ADD_MODE_STABLE: assume property (@(posedge clk) disable iff (!rstn) $stable(sig_ADD_MODE));
    ASM_PARAM_ADD_MODE_RANGE: assume property (@(posedge clk) disable iff (!rstn) sig_ADD_MODE==0 || sig_ADD_MODE==1);


   // masks for the parameter signals
   logic [max_FIFO_WIDTH -1:0]  width_msk;
   logic [max_NUM_LOOPS -1:0] num_loop_msk;                 

   assign width_msk = ('b1<<sig_FIFO_WIDTH) -1;
   assign num_loop_msk = ('b1<<sig_NUM_LOOPS) -1;
   

   // helper logic for data coloring 
   
   logic [max_FIFO_WIDTH -1:0] in_data; // driven data into the fifo
   logic [max_FIFO_WIDTH -1:0] expected_data; // the colored data expected from the DUT
   logic [max_NUM_LOOPS-1:0] shift_pop; // a shifter for the pop signals, used for the manipulation of the colored data


   always @(posedge clk or negedge rstn)
     if (!rstn) 
       begin
          in_data <= 'b0;
          expected_data <= 'b0;
       end
     else
       begin
          if (!full && push)
            in_data <= (in_data + 1) & width_msk; // colored data increments by 1
          if (!empty && pop)
            expected_data <= (expected_data +1) & width_msk; // colored data increments by 1
       end

   // shift the pop signal
   always @(posedge clk or negedge rstn)
     if (!rstn) 
       shift_pop <= 'b0;
     else
       shift_pop <= {shift_pop,pop} & num_loop_msk;

   
   default clocking dc @(posedge clk); endclocking
   default disable iff (!rstn);
   

   // fifo assumes
   ASM_underflow: assume property (empty |-> !pop);
   ASM_overflow: assume property (full |-> !push);

   // data coloring assumes
   ASM_input: assume property (!full && push |-> push_data == in_data);

   // output asserts
   AST_output_add: assert property (sig_ADD_MODE==1 && shift_pop[sig_NUM_LOOPS-1]
                                    |-> (pop_data == 
                              (width_msk & 
                              (expected_data - $countones(shift_pop)+sig_NUM_LOOPS))));

   AST_output_sub: assert property (sig_ADD_MODE==0 && shift_pop[sig_NUM_LOOPS-1]
                                    |-> (pop_data == 
                              (width_msk & 
                              (expected_data -  $countones(shift_pop)-sig_NUM_LOOPS))));
                              
   
   /////// DUT inst ///////
   fifo_with_sig#(
                  .max_FIFO_DEPTH (max_FIFO_DEPTH),
                  .max_FIFO_WIDTH (max_FIFO_WIDTH),
                  .max_NUM_LOOPS (max_NUM_LOOPS),
                  .max_ADD_MODE (max_ADD_MODE)
                  )
   u_dut
     (.*);




endmodule
