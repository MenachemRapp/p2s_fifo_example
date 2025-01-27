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
