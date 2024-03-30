/* 
Student Name : Abdullah Sami Naser          Student ID : 1201952 
Student Name : Majd Riyad Abdeddein         Student ID : 1202923 
Instructor : Dr.Aziz Qaroush , Dr.Ayman Hroub 
-----------------------------------------------------------------
Computer Architecture - Project 2 
-----------------------------------------------------------------
Single Cycle RISC Processor Design 
-----------------------------------------------------------------
This file contains all modules and their testbench
-----------------------------------------------------------------
*/ 	  



//1)
//-------------------------------Instruction Fetch Operations--------------------------------- 	
// --------------------> PC , TestBench , Instruction Memory , TestBench , PCAdder, PCMux 			   

//****************PC****************

`timescale 1ns / 1ps

module PCReg (
	input init,
    input clk,               
    input reset,             
    input [31:0] input_address,      
    output reg [31:0] output_address
);

    always @(posedge clk or negedge reset) begin
        if (!reset) 
            output_address <= 32'h0000_0000; 
        else begin 
			if (!init)
            output_address <= input_address; 
			else 
				output_address 	 =0;  
		end
    end										   
	
endmodule	

//****************PC Test Bench****************
//module PCReg_tb;
//
//  reg Tclk;             
//  reg Treset;           
//  reg [31:0] Tin;    
//  wire [31:0] Tout;  
//
//  // Instantiate the Program Counter
//  PCReg pc (
//    .clk(Tclk),
//    .reset(Treset),
//    .input_address(Tin),
//    .output_address(Tout)
//  );
//
//  initial begin
//    // Initialize signals
//    Tclk = 0;
//    Treset = 0;
//    Tin = 0;
//
//    // Apply reset
//    Treset = 0;
//    #90 Treset = 1;
//
//    // Apply a few PC values
//    #10 Tin = 32'h00000004;
//    #20 Tin = 32'h00000008;
//    #20 Tin = 32'h0000000C;
//
//    // End of test
//    #50 $finish;
//  end
//
//  always #10 Tclk = ~Tclk; // Generate clock signal
//
//  // Monitor the output
//  initial begin
//    $monitor("At time %d, pc_in = %h, pc_out = %h", $time, Tin, Tout);
//  end
//
//endmodule


//****************PCMux ****************
 
module PCMux(in0,in1,in2,in3,PCSrc,address);  
	 input [31:0]in0,in1,in2,in3; 
	 input [1:0]PCSrc;  
	 output reg [31:0] address;
	 always @(in0 or in1 or in2 or PCSrc) begin 
		 if(PCSrc == 0) 
			 address = in0;
		 else if (PCSrc == 1) 
			 address = in1;
		 else if (PCSrc == 2) 
			 address = in2; 
	     else 
			 address = in3;
	end 			 
	endmodule	   	 
	

//****************Instruction Memory****************			 
 module InstructionMemory (
  input [31:0] address,output reg [31:0] instruction);

  // Define the instruction memory
  reg [31:0] memory [255:0]; 

  // Fetch the instruction at the specified address
  always @(address) begin
    instruction = memory[address];
  end

  // Initialize the instruction memory
  initial begin
    // Load instructions into memory
     memory[0] = 32'b00001000010000100000000000101010; 
	 memory[1] = 32'b00001000000000000000001100100100; 
     memory[2] = 32'b00001000010001000010000000000000; 
	 
	 memory[100] = 32'b00001000010000100000000000010010; 
     memory[101] = 32'b00001000110001100000000000100010; 	
	 memory[102] = 32'b00001000000000000000011001000100; 
	 memory[103] = 32'b00001000000000000000000000001011;  
	 
	 memory[200] = 32'b00001000110001100000000000101011; 	

	  

  end										   
  

endmodule		

//****************PCAdder****************
module PCAdder(address,PCnext_address);
	input [31:0]address;
	output [31:0]PCnext_address;
	assign PCnext_address = address + 1;
endmodule

//***************************************************************************************

//2)
//-------------------------------Instruction Decode Operations--------------------------------- 	
// --------------------> Decode Unit , Control Unit , Register File,Extender and TestBench	





//****************Decode Unit****************
module InstructionDecodeUnit(instruction,typ,stop,func,rs1,rs2,rd,imm14,sa5,imm24);
	input [31:0] instruction; 
	output reg stop;
	output reg [1:0]typ;
	output reg [4:0] func,rs1,rs2,rd,sa5; 
	output reg [13:0]imm14;
	output reg [23:0]imm24;
	
	always @(*) begin
        case (instruction[2:1]) //according to type bits
            2'b00: begin // R-type
				func = instruction[31:27];
                rs1 = instruction[26:22];
                rd = instruction[21:17];
				rs2 = instruction[16:12];
                typ = instruction[2:1];
				stop= instruction[0];
            end
            2'b01: begin // I-type
                func = instruction[31:27];
                rs1 = instruction[26:22];
                rd = instruction[21:17];   
				imm14 = instruction[16:3];
				typ = instruction[2:1];
				stop = instruction[0];
            end
            2'b10: begin // J-type
                func = instruction[31:27]; 
				imm24 = instruction[26:3];
				typ	= instruction[2:1];
				stop = instruction[0];
            end
            2'b11: begin // S-type
                func = instruction[31:27];
                rs1 = instruction[26:22];
                rd = instruction[21:17];
				rs2 = instruction[16:12];
                sa5 = instruction[11:7];
				typ = instruction[2:1];
				stop= instruction[0];
            end	 
			default : begin 
				typ = 2'bxx;  
				end
        endcase
    end
endmodule

//****************Control Unit****************
module ControlUnit(typ,func,pc_in,reg_src,reg_write,sign_ext,Imm_sel, ALU_src, mem_rd, mem_wr, WB_data,ALU_op,push,pop,stop_bit);
	input [1:0] typ;						 
	input [4:0] func;  
	input stop_bit;
	output reg [1:0]pc_in;
	output reg reg_src,reg_write,sign_ext,Imm_sel,ALU_src,mem_rd,mem_wr,WB_data,push,pop;
	output reg[2:0] ALU_op;

	always @(*) 
		begin 
			if (typ==2'b00)  //R-type
				begin 
					if (stop_bit == 0)
						begin 
						pc_in =0; 
						push = 0;
						pop = 0;
						end 
					else 
						begin 
						pop = 1;
						push = 0;
						pc_in =3;
						end 
					reg_src = 0;
					reg_write = 1;
					sign_ext = 0; //dont care
					Imm_sel = 0; //dont care
					ALU_src = 0;
					mem_rd = 0;
					mem_wr= 0;
					WB_data = 0;
					case(func) 
						5'b00000: ALU_op = 3'b000; //AND 
						5'b00001: ALU_op = 3'b001; //ADD
						5'b00010: ALU_op = 3'b010; // SUB
						5'b00011: ALU_op = 3'b011; //CMP  
					endcase
				end 
			else if (typ == 2'b01) // I-type   
				begin 
				case(func) 
						5'b00000 : begin // ANDI 
							if (stop_bit == 0)
								begin 
									pc_in =0; 
									push = 0;
									pop = 0;
								end 
							else 
								begin 
									pop = 1;
									push = 0;
									pc_in =3;
								end 
							reg_src = 0; //don't care
							reg_write = 1;
							sign_ext = 0; 
							Imm_sel = 0;
							ALU_src = 1;
							mem_rd = 0;
							mem_wr= 0;
							WB_data = 0;
							ALU_op = 3'b000; //AND
						end  
						
						5'b00001 : // ADDI 
						begin 
							if (stop_bit == 0)
								begin 
									pc_in =0; 
									push = 0;
									pop = 0;
								end 
							else 
								begin 
									pop = 1;
									push = 0;
									pc_in =3;
								end 
							reg_src = 0; //don't care
							reg_write = 1;
							sign_ext = 1; 
							Imm_sel = 0;
							ALU_src = 1;
							mem_rd = 0;
							mem_wr= 0;
							WB_data = 0;  
							ALU_op = 3'b001; //ADD
						end 
						
						5'b00010 : // LW 
						begin 
							if (stop_bit == 0)
								begin 
									pc_in =0; 
									push = 0;
									pop = 0;
								end 
							else 
								begin 
									pop = 1;
									push = 0;
									pc_in =3;
								end 
							reg_src = 0; //don't care
							reg_write = 1;
							sign_ext = 1; 
							Imm_sel = 0;
							ALU_src = 1;
							mem_rd = 1;
							mem_wr= 0;
							WB_data = 1; 
							ALU_op = 3'b001; //ADD
						end 
						
						5'b00011 : // SW 
						begin 
							if (stop_bit == 0)
								begin 
									pc_in =0; 
									push = 0;
									pop = 0;
								end 
							else 
								begin 
									pop = 1;
									push = 0;
									pc_in =3;
								end 
							reg_src = 1; //Rd
							reg_write = 0;
							sign_ext = 1; 
							Imm_sel = 0;
							ALU_src = 1;
							mem_rd = 0;
							mem_wr= 1;
							WB_data = 0; // don't care 
							ALU_op = 3'b001; // ADD
						end 
						
						5'b00100 : // BEQ 
						begin 
							pc_in = 1;
							reg_src = 1;
							reg_write = 0;
							sign_ext = 1; 
							Imm_sel = 0;
							ALU_src = 0;
							mem_rd = 0;
							mem_wr= 0; 
							push =0;
							pop = 0;
							WB_data = 0; // don't care 
							ALU_op = 3'b100; //BEQ
						end   
				endcase
				end 
			else if (typ == 2'b10) //J-type 
					 begin 
					pc_in = 2;
					reg_src = 0;//dont care
					reg_write = 0; //dont care
					sign_ext = 0; //dont care
					Imm_sel = 0; //dont care
					ALU_src = 0; //dont care
					mem_rd = 0;	//dont care
					mem_wr= 0;	//dont care
					WB_data = 0; //dont care
					ALU_op = 3'b000;  //don't care
					if (func == 5'b00000) //J 
						begin 
							push=0;
							pop =0;
						end 
					else 
						begin 
							push = 1;
							pop = 0;
						end 
					 end 	
			else if (typ == 2'b11) //S-type 
					casex(func) 
							5'b0000x : 
							begin 
							if (stop_bit == 0)
								begin 
									pc_in =0; 
									push = 0;
									pop = 0;
								end 
							else 
								begin 
									pop = 1;
									push = 0;
									pc_in =3;
								end 
							reg_src = 0; //dont care 
							reg_write = 1;
							sign_ext = 0; 
							Imm_sel = 1;
							ALU_src = 1;
							mem_rd = 0;
							mem_wr= 0;
							WB_data = 0; 
							case(func[0]) 
								1'b0 : ALU_op = 3'b101; //SLL
								1'b1 : ALU_op = 3'b110;	//SLR 
							endcase
							end 	   
							
							5'b0001x : 
							begin 
							if (stop_bit == 0)
								begin 
									pc_in =0; 
									push = 0;
									pop = 0;
								end 
							else 
								begin 
									pop = 1;
									push = 0;
									pc_in =3;
							end 
							reg_src = 0;  
							reg_write = 1;
							sign_ext = 0; //dont care 
							Imm_sel = 0;  //dont care 
							ALU_src = 0;
							mem_rd = 0;
							mem_wr= 0;
							WB_data = 0; 
							case(func[0]) 
								1'b0 : ALU_op = 3'b101; //SLL
								1'b1 : ALU_op = 3'b110;	//SLR 
							endcase
							end 	  
				endcase	
			else
				begin 	
					// in order to handle irregular register or memory write and read 
					mem_rd = 0;
					mem_wr = 0;
					reg_write = 0;
				end 
			end 
							
endmodule


//****************Control Unit TB****************
//module cu_tb; 
//	reg [1:0] typ;						 
//	reg [4:0] func;  
//	wire [1:0]pc_in;
//	wire reg_src,reg_write,sign_ext,Imm_sel,ALU_src,mem_rd,mem_wr,WB_data;   
//	wire [2:0] ALU_op;
//	ControlUnit cu1(.typ(typ),.func(func),.pc_in(pc_in),.reg_src(reg_src),
//	.reg_write(reg_write),.sign_ext(sign_ext),.Imm_sel(Imm_sel),
//	.ALU_src(ALU_src), .mem_rd(mem_rd), .mem_wr(mem_wr), .WB_data(WB_data),.ALU_op(ALU_op));
//	
//	initial begin 
//		// Test R-type 
//		typ =2'b00; 
//		func = 5'b00000; 
//		
//		#10ns 
//		func = 5'b00011; 
//		
//		//Test I-Type
//		#10ns 	 
//		typ = 2'b01; 
//		func=5'b00000; 	
//		
//		#10ns 	 
//		func=5'b00001;
//		
//		#10ns 	 
//		func=5'b00010;
//		
//		#10ns 	 
//		func=5'b00011;
//		
//		#10ns 	 
//		func=5'b00100;
//		
//		//Test J-Type
//		#10ns 	 
//		typ = 2'b10; 
//		func=5'b00000;
//		
//		#10ns 	 
//		func=5'b00001; 
//		
//		
//		//Test S-Type 
//		#10ns 	 
//		typ = 2'b11; 
//		func=5'b00000;
//		
//		#10ns 	  
//		func=5'b00011;
//		
//		
//		
//		#20ns $finish; 
//		end 
//		
//endmodule		
		
		 
		
		



//****************Register File****************
module RegisterFile (ra,rb,rw,busW,regWrite,busA,busB,input clk,input init);
	input regWrite;
	input [4:0]ra,rb,rw;
	input [31:0]busW;
	output [31:0]busA,busB;
    // 32 registers, each 32 bits wide
    reg [31:0] registers [31:0]; 
	int i;

    // Write operation on rising edge of the clock
    always @(posedge clk) begin
        if (regWrite) 
            registers[rw]  <= busW;	
	end    
	
	always @(init) begin 
		if(init)
			for (i=0; i<32 ; i=i+1)
				registers[i] = 32'd0;
	end 
	
	assign busA = registers[ra];
	assign busB = registers[rb];
	initial begin 
		$monitor("At Time =%t ----> R0=%h, R1=%h, R2=%h, R3=%h, R4=%h, R5=%h, R6=%h",$time,registers[0],registers[1],registers[2],registers[3],registers[4],
		registers[5],registers[6]);	  
		end 
	endmodule
 

//****************Register File TestBench****************
//module RegFiletb;
//	reg regWrite;
//	reg [4:0]ra,rb,rw; 
//	reg [31:0]busW;
//	wire [31:0]busA,busB; 
//	
//	RegisterFile rf1(.ra(ra),.rb(rb),.rw(rw),.busW(busW),.regWrite(regWrite),.busA(busA),.busB(busB));
//	
//	initial begin 
//		// initialize 
//		regWrite =0;
//		ra =0;
//		rb=0;
//		rw=0; 
//		busW =0;
//		
//		// write to reg 
//		#10ns 
//		regWrite = 1;
//		ra =0;
//		rb =0; 
//		rw=0;
//		busW = 12;	
//		
//		//write to reg 	
//		#20ns 
//		rw=1;
//		busW = 13;	 
//		
//		//write to reg 	
//		#20ns 
//		rw=2;
//		busW = 14;
//		
//		
//		// read   
//		#20ns 
//		ra =0;
//		rb = 1; 
//		regWrite =0;
//		
//		
//		#40ns $finish;
//		
//	end 
//endmodule


//****************Extender****************
module Extender (
    input [13:0] imm, // 14-bit immediate
    input [4:0] sa, // 5-bit shift amount
    input imm_sa_sel, 
    input signOp,
    output reg [31:0] extended_output 
);	  
    always @(imm, sa, imm_sa_sel, signOp) begin 
        if (imm_sa_sel) begin 
            extended_output[4:0] = sa;
            if (signOp) 
                extended_output[31:5] = {27{sa[4]}};
            else 
                extended_output[31:5] = {27'b0}; 
        end else begin 
            extended_output[13:0] = imm;
            if (signOp) 
                extended_output[31:14] = {18{imm[13]}};
            else 
                extended_output[31:14] = {18'b0};	 
        end 	
    end

endmodule			 

//****************Extender TB****************
//module ext_tb; 
//	reg [13:0] timm;
//	reg [4:0] sa; 
//	reg imm_sa_sel;
//	reg signOp;
//	wire [31:0]out;	 
//	Extender ext(.imm(timm),.sa(sa),.imm_sa_sel(imm_sa_sel),.signOp(signOp),.extended_output(out));
//	
//	initial begin 
//		timm=14'b10000000000000;
//		sa=5'd16;
//		imm_sa_sel=0;
//		signOp=1;
//		
//		#10ns 
//		 imm_sa_sel=1;
//		signOp=1; 
//		
//		#10ns
//		imm_sa_sel=0;
//		signOp=0;
//		
//		#10ns
//		imm_sa_sel=1;
//		signOp=0;
//		
//		
//		#10ns $finish; 
//		
//	end 
//endmodule
//


//3)
//-------------------------------Excution Operations--------------------------------- 	
// --------------------> ALU , TestBench , BranchControlUnit 

//****************NextPCControl Unit****************

module NextPCControlUnit(pc_in,zero,PCSrc,out_pc,PCin0,PCin1,PCin2,PCin3,extended_imm14,imm24,ra);	 //must be delayed to be finish after ALU end its operation 
	input [1:0]pc_in;
	input zero;		
	input [31:0] out_pc; 
	input [31:0] ra;
	input [31:0]extended_imm14;
	input [23:0]imm24;
	output reg[1:0]PCSrc; 					   
	output reg [31:0]PCin0,PCin1,PCin2,PCin3;
	
	// check the pc_in 
	
	always @(*) 
		begin 
			if(pc_in == 1) 		   //Branch case
				begin 
					if (zero) 
						PCSrc = pc_in; 
					else 
						PCSrc = 0; 
				end 
			else 
				PCSrc = pc_in;
		end  
		
	assign PCin0 = out_pc + 1, 
	PCin1 = out_pc + 1 + extended_imm14, 
	PCin2 =  {out_pc[31:24],imm24},
	PCin3 = ra;

		
endmodule  



//****************ALU****************
module ALU(i1, i2, ALU_op, ALU_out,zero);
	input [31:0]i1,i2;	
	input [2:0] ALU_op;
	output reg [31:0] ALU_out;
	output reg zero;
	
	always @(*) begin
		case (ALU_op)
			5'b000:	ALU_out = i1 & i2;   //AND 
			5'b001: ALU_out = i1 + i2; 	//ADD 
			5'b010: ALU_out = i1-i2;   //SUB
			5'b011: begin 	 //CMPLS
				if(i1 < i2)	begin 
					ALU_out= i1-i2;	  //
					zero = 1;  
					end 
				else   begin 
					ALU_out = i1-i2;
					zero=0;	
					end 
				end 
			5'b100: begin  //EQ
				if(i1 == i2)	begin 
					ALU_out= i1-i2;
					zero = 1; 
					end 
				else  begin 
					ALU_out = i1-i2;
					zero=0;
					end 
				end   
			5'b101: ALU_out = i1 << i2; //SLL
			5'b110: ALU_out = i1 >> i2; //SLR
		endcase
	end 
endmodule

//****************ALU TB****************  
//module ALU_tb;
//	reg [31:0]i1,i2;	
//	reg [2:0] ALU_op;
//	wire [31:0] ALU_out;
//	wire zero;	 
//	
//	ALU a1(.i1(i1), .i2(i2), .ALU_op(ALU_op), .ALU_out(ALU_out),.zero(zero));
//	
//	initial begin 
//		// Test and 
//		i1 = 5;
//		i2 = 9;
//		ALU_op = 3'b000;
//		
//		
//		// Test add
//		#10ns
//		ALU_op = 3'b001;
//		
//		// Test sub
//		#10ns
//		ALU_op = 3'b010;
//		
//		// Test cmp
//		#10ns
//		ALU_op = 3'b011;
//		
//		// Test branch
//		#10ns
//		ALU_op = 3'b100;
//		
//		// Test sll
//		#10ns
//		ALU_op = 3'b101;
//		
//		// Test slr
//		#10ns
//		ALU_op = 3'b110;
//		
//		
//		#20ns $finish;
//	end 
//endmodule
//		


//4&5)
//-------------------------------Memory and WB Operations--------------------------------- 	
// --------------------> Data Memory , WB , Stack


module DataMemory (clk,reset,mem_read,mem_write,data_in,address,data_out);
	input mem_read,mem_write,reset,clk;
	input [31:0] address,data_in;
	output reg [31:0] data_out; 	   
	reg [31:0] memory [511:0]; // 512 cell , 32 bit each (smaller memory) 
	
	// perform operations read,write,reset or noop 
	always @(negedge clk) begin 
		if (!reset) 
			memory = '{512{32'd0}};	 
		else 
			begin 
				if (mem_read == 1)
					data_out = memory[address]; 
				else if (mem_write == 1)	  
					memory[address] = data_in; 
			end 
	
		end 
	initial begin 
		$monitor("Time = %t , Mem[0] = %h, Mem[1] = %h , Mem[2] = %h",$time,memory[0],memory[1],memory[2]);	
		end
	endmodule		
	
//--------------------- Memory TB
//module DataMemory_tb;
//	reg tmem_read,tmem_write,treset; 
//	reg [31:0] taddress,tdata_in; 
//	wire [31:0]tdata_out; 
//	
//	DataMemory dm1(.reset(treset),.mem_read(tmem_read),.mem_write(tmem_write), 
//	.data_in(tdata_in),.data_out(tdata_out),.address(taddress)); 
//	
//	initial begin  
//		//initial values 
//		tmem_read = 0;
//		tmem_write = 0;
//		treset = 1; 
//		taddress = 0;
//		tdata_in=0;
//		
//		// write operation 
//		#10ns 
//		tmem_write = 1;
//		taddress = 1; 
//		tdata_in = 12; 
//		
//		// write operation
//		#20ns 
//		taddress = 2; 
//		tdata_in = 13;
//		
//		// write operation
//		#20ns 
//		taddress = 3; 
//		tdata_in = 14;
//		
//		// write operation
//		#20ns 
//		taddress = 4; 
//		tdata_in = 15;
//		
//		// read operation 
//		#20ns 
//		tmem_write =0;
//		tmem_read = 1;
//		taddress = 3;
//		
//		// finish 
//		#30 $finish;
//	end 
//
//endmodule				 
//----------------------------------Stack 
// -1 
module stack_memory(clk,push,pop,ra_in,ra_out);
	input clk,push,pop;
	input [31:0]ra_in;	
	reg [4:0]sp =0 ;
	output reg [31:0]ra_out;
	
	parameter depth = 32;
	reg [31:0] stack [0:depth-1];
	// perform operations read,write,reset or noop 
	 always @(negedge clk) begin
        if (push && sp < depth) begin
            // Push data onto the stack
            stack[sp] <= ra_in;
            sp <= sp + 1;
        end else if (pop && sp > 0) begin
            // Pop data from the stack
            sp <= sp - 1;
        end
    end
	assign ra_out = (sp > 0) ? stack[sp-1] : 32'b0;
	endmodule	
	

//-------------------------------Other Components : MUXes --------------------------------- 
module mux2to1(i0,i1,s,f);
	input [31:0]i0,i1;
	input s;
	output reg [31:0] f;
	
	always @(s or i0 or i1) begin 
		if(s) 
			f = i1;
		else 
			f=i0;
	end
endmodule	  
//-------------------------------

module mux2to1_5bit(i0,i1,s,f);
	  input [4:0]i0,i1;
	input s;
	output reg [4:0] f;
	
	always @(s or i0 or i1) begin 
		if(s) 
			f = i1;
		else 
			f=i0;
	end
endmodule	  


//-------------------------------Connect Datapath ---------------------------------
module DataPath;
	//clock and reset (basic inputs for the datapath)  
	reg clk; 
	reg reset;   
	reg init;	
	reg regfile_init;
	
// ********** DECODE *****************
	// pc input address and output addressed
    wire [31:0] input_address;      
    wire [31:0] output_address;	 
	
	// input for Instruction memory and output 
		// input is pc_out 
	wire [31:0] instruction; 		
	
	// input and output for instruction decode unit
		// input is instruction 
	wire stop;
	wire [1:0]typ;
	wire [4:0] func,rs1,rs2,rd,sa5; 
	wire [13:0]imm14;
	wire [23:0]imm24;		 
	
	// input and output of control unit -----> DELAY MUST BE AFTER HERE  
	      // input for cu is type and func,stop 
	wire [1:0]pc_in;
	wire reg_src,reg_write,sign_ext,Imm_sel,ALU_src,mem_rd,mem_wr,WB_data,push,pop;
	wire [2:0] ALU_op; 	
	
	
	// call the stack 
	       //input of stack push ,pop ,output_address +1,clk 
	wire [31:0] ra_out;	
		   
		   
		   
	// input and outputs for extender 
		// input is sa5,imm14,sign_ext,Imm_sel 
	wire [31:0] extended_output;    
	
	// input and outputs for mux before rb 
		//inputs are rd,rs2 and reg_src 
	wire [4:0] rb; //output of mux
		
	// input and outputs for RegFile 
		// inputs are ra,rb,rw,busW,regWrite
	    wire [31:0]busW;   	  
	wire [31:0]busA,busB;	 //outputs of reg file 
	
	
	// input and output of mux before ALU 
	     // input is extended output,busB,ALU_src
	wire [31:0]ALU_in2; //output of mux 
	
	// input and output of ALU 
	      //inputs are busA and ALU_in2 and ALU_op
	wire [31:0] ALU_out;
	wire zero;		   
	
	// input for NextPCcontrolunit and output 
		// inputs are zero,pc_in,output_address,imm24,extended_output,ra_out
	wire[1:0]PCSrc; 					   
	wire [31:0]PCin0,PCin1,PCin2,PCin3;;		
	
	//inputs for PCMux
		//inputs are PCSrc,PCin0,PCin1,PCin2,PCin3
	    // output is the input address for pc 
			
	
	// inputs for Data Memory and outputs 
		//inputs are ALU_out and mem_rd,mem_wr and busB
	wire [31:0] data_out;  
	
	// inputs for WBMux and outputs 
		// inputs are data_out,ALU_out,WB_data 
		// output is busW 
		
//************************ CALL MODULES 
 




PCReg pc1( 
	.init(init),
    .clk(clk),               
    .reset(reset),             
    .input_address(input_address),      
    .output_address(output_address)
);	



InstructionMemory im1(
         .address(output_address),
		 .instruction(instruction));	
		 

		 
InstructionDecodeUnit id1(
		.instruction(instruction),.typ(typ),
		.stop(stop),.func(func),
		.rs1(rs1),.rs2(rs2),
		.rd(rd),.imm14(imm14),
		.sa5(sa5),.imm24(imm24)); 
		

ControlUnit cu1(
		.typ(typ),.func(func),
		.pc_in(pc_in),.reg_src(reg_src),
		.reg_write(reg_write),.sign_ext(sign_ext),
		.Imm_sel(Imm_sel), .ALU_src(ALU_src),
		.mem_rd(mem_rd), .mem_wr(mem_wr),
		.WB_data(WB_data),
		.ALU_op(ALU_op),
		.pop(pop),
		.push(push),
		.stop_bit(stop));	 
	
stack_memory  st1(.clk(clk),
.push(push),.pop(pop),
.ra_in(output_address + 1),
.ra_out(ra_out));
		
Extender ex1(
    .imm(imm14), 
    .sa(sa5), 
    .imm_sa_sel(Imm_sel), 
    .signOp(sign_ext),
     .extended_output(extended_output) 
);	  


mux2to1_5bit m1(
.i0(rs2),
.i1(rd),
.s(reg_src),
.f(rb));


RegisterFile rf1(  
.init(regfile_init),
.clk(clk),
.ra(rs1),.rb(rb),
.rw(rd),.busW(busW),
.regWrite(reg_write),.busA(busA),
.busB(busB));



mux2to1 m2(
.i0(busB),
.i1(extended_output),
.s(ALU_src),
.f(ALU_in2)); 


ALU  al1(	
.i1(busA),
.i2(ALU_in2),
.ALU_op(ALU_op),
.ALU_out(ALU_out),
.zero(zero));



NextPCControlUnit npc1(
.pc_in(pc_in),.zero(zero),
.PCSrc(PCSrc),.out_pc(output_address),
.PCin0(PCin0),.PCin1(PCin1),
.PCin2(PCin2),.extended_imm14(extended_output),
.imm24(imm24),.PCin3(PCin3),.ra(ra_out));	



PCMux  pcm1(
.in0(PCin0),.in1(PCin1),
.in2(PCin2),.PCSrc(PCSrc),
.in3(PCin3),
.address(input_address));

DataMemory  dm1(  
.clk(clk),
.reset(reset),.mem_read(mem_rd),
.mem_write(mem_wr),.data_in(busB),
.address(ALU_out),.data_out(data_out));


mux2to1 m3(
.i0(ALU_out),
.i1(data_out),
.s(WB_data),
.f(busW));





initial begin 
	clk = 0	;
reset = 1;
init=1; 
regfile_init = 0;

#400ns 
init = 0;		
regfile_init = 1;

#20000ns $finish;
end 
always begin 
	#200ns begin 
		clk = ~clk;	
end  
end
endmodule


