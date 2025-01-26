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
   

    ASM_PARAM_FIFO_DEPTH_STABLE: assume property (@(posedge clk) disable iff (!rstn) $stable(sig_FIFO_DEPTH));
    ASM_PARAM_FIFO_DEPTH_RANGE: assume property (@(posedge clk) disable iff (!rstn) sig_FIFO_DEPTH==2 || sig_FIFO_DEPTH==4 || sig_FIFO_DEPTH==8);
    ASM_PARAM_FIFO_WIDTH_STABLE: assume property (@(posedge clk) disable iff (!rstn) $stable(sig_FIFO_WIDTH));
    ASM_PARAM_FIFO_WIDTH_RANGE: assume property (@(posedge clk) disable iff (!rstn) sig_FIFO_WIDTH==8 || sig_FIFO_WIDTH==9 || sig_FIFO_WIDTH==10 || sig_FIFO_WIDTH==11);
    ASM_PARAM_NUM_LOOPS_STABLE: assume property (@(posedge clk) disable iff (!rstn) $stable(sig_NUM_LOOPS));
    ASM_PARAM_NUM_LOOPS_RANGE: assume property (@(posedge clk) disable iff (!rstn) sig_NUM_LOOPS==3 || sig_NUM_LOOPS==4 || sig_NUM_LOOPS==5 || sig_NUM_LOOPS==6);
    ASM_PARAM_ADD_MODE_STABLE: assume property (@(posedge clk) disable iff (!rstn) $stable(sig_ADD_MODE));
    ASM_PARAM_ADD_MODE_RANGE: assume property (@(posedge clk) disable iff (!rstn) sig_ADD_MODE==0 || sig_ADD_MODE==1);
 
                              

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
