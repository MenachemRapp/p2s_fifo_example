module fifo_with_sig #
(
  parameter max_FIFO_DEPTH = 8,
  parameter max_FIFO_WIDTH = 11,
  parameter max_NUM_LOOPS = 6,
  parameter max_ADD_MODE = 1
)
(
  input clk,
  input rstn,
  input push,
  input [max_FIFO_WIDTH-1:0] push_data,
  input pop,
  output reg [max_FIFO_WIDTH-1:0] pop_data,
  output reg empty,
  output reg full,
  input [$clog2(max_FIFO_DEPTH):0] sig_FIFO_DEPTH,
  input [$clog2(max_FIFO_WIDTH):0] sig_FIFO_WIDTH,
  input [$clog2(max_NUM_LOOPS):0] sig_NUM_LOOPS,
  input sig_ADD_MODE
);

  wire [max_FIFO_WIDTH-1:0] msk_push_data;
  wire [max_FIFO_WIDTH-1:0] msk_pop_data;
  wire [max_FIFO_WIDTH-1:0] msk_pop_data_internal;
  wire [max_FIFO_WIDTH-1:0] msk_mem;
  wire [$clog2(max_FIFO_DEPTH)-1:0] msk_wptr;
  wire [$clog2(max_FIFO_DEPTH)-1:0] msk_rptr;
  wire [$clog2(max_FIFO_DEPTH)-1:0] msk_level;
  wire [max_NUM_LOOPS-1:0] msk_pipe_data;
  wire [max_NUM_LOOPS:1] msk_pop_shift;
  assign msk_push_data = (1'b1 << sig_FIFO_WIDTH - 1 - 0 + 1) - 'b1;
  assign msk_pop_data = (1'b1 << sig_FIFO_WIDTH - 1 - 0 + 1) - 'b1;
  assign msk_pop_data_internal = (1'b1 << sig_FIFO_WIDTH - 1 - 0 + 1) - 'b1;
  assign msk_mem = (1'b1 << sig_FIFO_WIDTH - 1 - 0 + 1) - 'b1;
  assign msk_wptr = sig_FIFO_DEPTH - 'b1;
  assign msk_rptr = sig_FIFO_DEPTH - 'b1;
  assign msk_level = sig_FIFO_DEPTH - 'b1;
  assign msk_pipe_data = (1'b1 << sig_NUM_LOOPS - 1 - 0 + 1) - 'b1;
  assign msk_pop_shift = (1'b1 << sig_NUM_LOOPS - 1 + 1) - 'b1;
  integer i;
  reg [max_FIFO_WIDTH-1:0] pop_data_internal;
  reg [max_FIFO_WIDTH-1:0] mem [max_FIFO_DEPTH-1:0];
  reg [$clog2(max_FIFO_DEPTH)-1:0] wptr;
  reg [$clog2(max_FIFO_DEPTH)-1:0] rptr;
  reg [$clog2(max_FIFO_DEPTH)-1:0] level;

  always @(posedge clk or negedge rstn) if(!rstn) begin
    wptr <= 0;
    rptr <= 0;
  end else begin
    if(push) begin
      mem[wptr & msk_wptr] <= push_data & msk_push_data;
      wptr <= (wptr & msk_wptr) + 1'b1;
    end 
    if(pop) rptr <= (rptr & msk_rptr) + 1'b1; 
  end


  always @(*) begin
    pop_data_internal = mem[rptr & msk_rptr] & msk_mem;
    empty = (wptr & msk_wptr) == (rptr & msk_rptr);
    level = ((wptr & msk_wptr) >= (rptr & msk_rptr))? (wptr & msk_wptr) - (rptr & msk_rptr) : (wptr & msk_wptr) + sig_FIFO_DEPTH - (rptr & msk_rptr);
    full = (level & msk_level) == sig_FIFO_DEPTH - 1;
  end

  reg [max_NUM_LOOPS-1:0] pipe_data [max_FIFO_WIDTH-1:0];
  reg [max_NUM_LOOPS:1] pop_shift;

  always @(posedge clk or negedge rstn) if(!rstn) begin
    pop_shift <= 0;
    for(i=0; (i<sig_NUM_LOOPS)&&(i<max_NUM_LOOPS); i=i+1) pipe_data[i] <= 0;
  end else begin
    pop_shift <= { pop_shift & msk_pop_shift, pop };
    for(i=max_NUM_LOOPS-1; i>0; i=i-1) if(i <= sig_NUM_LOOPS - 1) if(pop_shift[i]) if(sig_ADD_MODE == 1) pipe_data[i] <= (pipe_data[i - 1] & msk_pipe_data) + 1; 
    else pipe_data[i] <= (pipe_data[i - 1] & msk_pipe_data) - 1; 
    if(pop) if(sig_ADD_MODE == 1) pipe_data[0] <= (pop_data_internal & msk_pop_data_internal) + 1; 
    else pipe_data[0] <= (pop_data_internal & msk_pop_data_internal) - 1; else pipe_data[0] <= 0;
  end

  assign pop_data = pipe_data[sig_NUM_LOOPS - 1] & msk_pipe_data;

endmodule

