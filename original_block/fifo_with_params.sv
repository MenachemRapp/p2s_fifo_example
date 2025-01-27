
module fifo_with_params
  #(
    parameter FIFO_DEPTH = 8,
    parameter FIFO_WIDTH = 11,
    parameter NUM_LOOPS  = 3,
    parameter ADD_MODE   = 1
    )
   (
    input                         clk ,
    input                         rstn ,
    input                         push ,
    input [FIFO_WIDTH-1:0]        push_data ,
    input                         pop ,
    output reg [FIFO_WIDTH-1:0] pop_data ,
    output reg                  empty ,
    output reg                  full 
    );

   
   reg [FIFO_WIDTH-1:0]         pop_data_internal;
   
   reg [FIFO_WIDTH-1:0]         mem [FIFO_DEPTH-1:0];
   reg [$clog2(FIFO_DEPTH)-1:0]   wptr;
   reg [$clog2(FIFO_DEPTH)-1:0]   rptr;
   reg [$clog2(FIFO_DEPTH)-1:0]   level;
   

   always @(posedge clk or negedge rstn)
     if (!rstn)
       begin
	  wptr <= 0;
	  rptr <= 0;
       end
     else
       begin
	  if (push)
	    begin
	       mem[wptr] <= push_data;
	       wptr <= wptr + 1'b1;
            end
	  
	  if (pop)
	    rptr <= rptr + 1'b1;
       end

   always_comb
     begin
        pop_data_internal = mem[rptr];

        empty       = (wptr == rptr);
        
        level       = (wptr >= rptr) ?
                      (wptr - rptr) : 
                      (wptr + FIFO_DEPTH - rptr);
        
        full        = (level == FIFO_DEPTH-1);
        
     end

   
   reg [FIFO_WIDTH-1:0] pipe_data [NUM_LOOPS-1:0] ;
   reg [NUM_LOOPS:1]                   pop_shift;
   
   always @(posedge clk or negedge rstn)
     if (!rstn)
       begin
          pop_shift <= 0;
          for (int i=0; i<NUM_LOOPS; i=i+1)
            pipe_data[i]                 <= 0;
       end
     else
       begin
          // shift left, lose MSB
          pop_shift <= {pop_shift, pop};

          for (int i=NUM_LOOPS-1; i>0; i=i-1)
            if (pop_shift[i])
              if (ADD_MODE==1)
                pipe_data[i] <= pipe_data[i-1] + 1;
              else
                pipe_data[i] <= pipe_data[i-1] - 1;
          
          if (pop)
            if (ADD_MODE==1)
              pipe_data[0] <= pop_data_internal + 1;
            else
              pipe_data[0] <= pop_data_internal - 1;
          else
            pipe_data[0] <= 0;
       end

   assign pop_data = pipe_data[NUM_LOOPS-1];
   

endmodule
