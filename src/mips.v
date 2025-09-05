//
//             MMXXV September 5 PUBLIC DOMAIN by JML
//
//      The authors and contributors disclaim copyright, 
//      patents and all related rights to this software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
// OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT OF ANY PATENT, COPYRIGHT, TRADE SECRET OR OTHER
// PROPRIETARY RIGHT.  IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR
// ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF
// CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
// WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//
//

// https://github.com/rolandbernard/kleine-riscv
// https://chipmunklogic.com/digital-logic-design/designing-pequeno-risc-v-cpu-from-scratch-part-3-dealing-with-pipeline-hazards/
// 

module riscv (
    input          I_clk,        // Clock
    input          I_rst,        // Reset (synchronous, active high)
    input	   I_stall,
    output reg [31:0] O_imem_addr,  // Instruction memory address
    input  [31:0] I_imem_data,  // Instruction memory data
    output reg [31:0] O_dmem_addr,  // Data memory address
    input  [31:0] I_dmem_rdata, // Data memory read data
    output reg [31:0] O_dmem_wdata, // Data memory write data
    output reg [3:0]  O_dmem_wmask, // Data memory write mask (byte-enable)
    output reg O_dmem_rd,     // Data memory read enable
    output reg O_dmem_we     // Data memory write enable
);

// Hazard
reg take_branch;
reg [5:0]  opcode;
reg [5:0]  special;
reg [4:0]  bcond;

// stage 1: IF instruction fetch
reg [31:0] instr;
reg [31:0] pc;
reg [31:0] next_pc;
reg [31:0] pc_if;

wire stall;
assign stall = 0; //I_stall;
reg invalidate_if;
always @* begin
	case (opcode)
	6'h2: invalidate_if <= 1; // J
	6'h3: invalidate_if <= 1; // JAL
	6'h0: begin
		case (special)
		6'h8: invalidate_if <= 1; // JR
		6'h9: invalidate_if <= 1; // JALR
		default: invalidate_if <= 0;
		endcase
		end
	6'h1: begin
		case (bcond)
		5'h0: invalidate_if <= take_branch; // BLTZ
		5'h1: invalidate_if <= take_branch; // BGEZ
		5'h10: invalidate_if <= take_branch; // BLTZAL
		5'h11: invalidate_if <= take_branch; // BGEZAL
		default: invalidate_if <= 0;
		endcase
		end
	6'h4: invalidate_if <= take_branch; // BEQ
	6'h5: invalidate_if <= take_branch; // BNE
	6'h6: invalidate_if <= take_branch; // BLEZ
	6'h7: invalidate_if <= take_branch; // BGTZ
	default: invalidate_if <= 0;
	endcase
end

always @(posedge I_clk) begin
        if (I_rst) begin
	$display("reset");
            	pc <= 32'h0;
		instr <= 32'h0;
		O_imem_addr <= 32'h0;
        end else if (stall) begin
        end else if (invalidate_if) begin
		instr <= 32'h0;
		pc <= next_pc;
		O_imem_addr <= next_pc;
        end else begin
		pc <= next_pc;
		O_imem_addr <= next_pc;
		instr <= I_imem_data;
        end
	pc_if <= pc;
	$display("I %h after %h stall:%h next_pc:%h", invalidate_if, pc, stall, next_pc);
end

// stage 2 : ID instruction decode and register fetch
// ==== Instruction Decode Wires ====
//reg [6:0]  opcode;
//reg [5:0]  special;
//reg [4:0]  bcond;
reg [4:0]  rd;
reg [9:0]  code;
reg [24:0] cofun;
// Immediate decode
reg [31:0] immediate;
wire [31:0] signed_immediate;
reg [31:0] code_offset;
reg [31:0] data_offset;
reg [31:0] target;
reg [31:0] imm_i;
reg [31:0] imm_s;
reg [31:0] imm_b;
reg [31:0] imm_u;
reg [31:0] imm_j;
// ==== Registers ====
reg [31:0] regfile [0:31];
reg [31:0] rsv;
reg [31:0] rtv;
reg [4:0] shamt;

reg [31:0] pc_id;

reg  invalidate_id;
always @(posedge I_clk)  begin
	invalidate_id <= invalidate_if;
end

assign signed_immediate = data_offset;

integer i;
always @(posedge I_clk) begin
        if (I_rst) begin
		rsv <= 32'h0;
		rtv <= 32'h0;
		opcode <=6'h0;
		rd <= 5'h0;
            	for (i = 0; i < 32; i = i+1) regfile[i] <= 0;
        end else if (stall) begin
        end else if (invalidate_id || invalidate_if) begin
		rsv <= 32'h0;
		rtv <= 32'h0;
		opcode <= 7'h0; 
		rd <= 5'h0;
	end else begin
    		// ==== Main Register Read ====
		rsv <= (instr[25:21] == 0) ? 32'b0 : regfile[instr[25:21]];
		rtv <= (instr[20:16] == 0) ? 32'b0 : regfile[instr[20:16]];
		opcode <= instr[31:26];
		rd <= instr[15:11];
        end
	bcond <= instr[20:16];
	special <= instr[5:0];
	pc_id <= pc_if;
	shamt <= instr[10:6]; 
	code   <= instr[25:6];
	cofun   <= instr[24:0];
	immediate <= {16'b0,instr[15:0]};
	target <= {pc_if[31:28],instr[25:0],2'b0}; // FIXME check PC
	code_offset <= {{14{instr[15]}}, instr[15:0], 2'b0};
	data_offset <= {{16{instr[15]}}, instr[15:0]};
end

// stage 3 : EX execute and effective address calculation
// ==== ALU ====
// Shifter
wire [31:0] shift1l;
wire [31:0] shift2l;
wire [31:0] shift4l;
wire [31:0] shift8l;
wire [31:0] shift16l;
wire [31:0] shift1r;
wire [31:0] shift2r;
wire [31:0] shift4r;
wire [31:0] shift8r;
wire [31:0] shift16r;
wire [15:0] fills;

assign shift1l = (shamt[0] == 1) ? {rtv[30:0],1'b0} : rtv;
assign shift2l = (shamt[1] == 1) ? {shift1l[29:0],2'b00} : shift1l;
assign shift4l = (shamt[2] == 1) ? {shift2l[27:0],4'b0000} : shift2l;
assign shift8l = (shamt[3] == 1) ? {shift4l[23:0],8'h00} : shift4l;
assign shift16l = (shamt[4] == 1) ? {shift8l[15:0],16'h0000} : shift8l;
assign fills = ((special == 6'h3 /*SRA*/ || special == 6'h7 /*SRAV*/)
	&& rtv[31] == 1'b1) ? 16'b1111_1111_1111_1111 : 
	16'b0000_0000_0000_0000;
assign shift1r = (shamt[0] == 1) ? {fills[0],rtv[31:1]} : rtv;
assign shift2r = (shamt[1] == 1) ? {fills[1:0],shift1r[31:2]} : shift1r;
assign shift4r = (shamt[2] == 1) ? {fills[3:0],shift2r[31:4]} : shift2r;
assign shift8r = (shamt[3] == 1) ? {fills[7:0],shift4r[31:8]} : shift4r;
assign shift16r = (shamt[4] == 1)?{fills[15:0],shift8r[31:16]} : shift8r;

reg [31:0] alu_out;

reg [6:0]  opcode_ex;
reg [4:0]  rd_ex;
reg [31:0] imm_u_ex;
reg [31:0] pc_ex;
reg [2:0]  funct3_ex;
reg [31:0] dmem_addr_ex;

reg [31:0] dmem_wmask;

always @* begin
	case (opcode)
	6'h1: begin
		case (bcond)
		5'h0: take_branch <= rsv[31] == 1'b1; // BLTZ
		5'h1: take_branch <= rsv[31] == 1'b0; // BGEZ
		5'h10: take_branch <= rsv[31] == 1'b1; // BLTZAL
		5'h11: take_branch <= rsv[31] == 1'b0; // BGEZAL
		default: take_branch <= 0;
		endcase
		end
       	6'h4: take_branch <= rsv == rtv; // BEQ
       	6'h5: take_branch <= rsv != rtv; // BNE
       	6'h6: take_branch <=  (rsv[31] == 1'b1) || (rsv == 32'h0); // BLEZ
       	6'h7: take_branch <=  (rsv[31] == 1'b0) && (rsv != 32'h0); // BGTZ
	default: take_branch <= 0;
	endcase
end

always @* begin
        if (I_rst) begin
        	next_pc <= 32'h0;
	end else begin
		next_pc <= (pc + 4);
// FIXME
		case (opcode)
		6'h0: begin
			case (special)
			6'h8: invalidate_if <= 1; // JR
			6'h9: invalidate_if <= 1; // JALR
			default: invalidate_if <= 0;
			endcase
			end
		6'h1: begin
			case (bcond)
			5'h0: invalidate_if <= take_branch; // BLTZ
			5'h1: invalidate_if <= take_branch; // BGEZ
			5'h10: invalidate_if <= take_branch; // BLTZAL
			5'h11: invalidate_if <= take_branch; // BGEZAL
			default: invalidate_if <= 0;
			endcase
			end
		6'h2: invalidate_if <= 1; // J
		6'h3: invalidate_if <= 1; // JAL
		6'h4: invalidate_if <= take_branch; // BEQ
		6'h5: invalidate_if <= take_branch; // BNE
		6'h6: invalidate_if <= take_branch; // BLEZ
		6'h7: invalidate_if <= take_branch; // BGTZ
		default: invalidate_if <= 0;
		endcase

	 	case (opcode)
		7'b1101111: begin
				next_pc <= pc_ex + imm_j; //JAL
			end
		7'b1100111: begin
			       	next_pc <= (rv1 + imm_i ) & ~1; //JALR
			end
        	7'b1100011: begin // Branch
				if (take_branch) begin
					next_pc <= pc_ex + imm_b;
				end
			end
		endcase
	end
end

reg  invalidate_ex;
always @(posedge I_clk)  begin
	invalidate_ex <= invalidate_id;
end

always @(posedge I_clk) begin
        if (I_rst) begin
        	alu_out <= 32'b0;
		O_dmem_rd <= 0;
		O_dmem_we <= 0;
		O_dmem_wmask <= 4'b0000;
		O_dmem_wdata <= 32'h0;
		O_dmem_addr <= 32'h0;
        end else if (stall) begin
	end else if (invalidate_ex || invalidate_if) begin
		opcode_ex <= 7'h0;
	end else begin
		O_dmem_wdata <= 32'h0;
		O_dmem_wmask <= 4'b0000;
		O_dmem_rd <= 0;
		O_dmem_we <= 0;
		alu_out <= 32'b0;
        	case (opcode)
		7'b1101111: begin
				//JAL
			end
		7'b1100111: begin
			       //JALR
			end
            	7'b0110011: begin // R-type
                	case ({funct7, funct3})
                    	{7'b0000000,3'b000}: alu_out <= rv1 + rv2; // ADD
                    	{7'b0100000,3'b000}: alu_out <= rv1 - rv2; // SUB
                    	{7'b0000000,3'b001}: alu_out <= rv1 << rv2[4:0]; // SLL
                    	{7'b0000000,3'b010}: alu_out <= 
			    ($signed(rv1) < $signed(rv2)) ? 32'b1 : 32'b0; //SLT
                    	{7'b0000000,3'b011}: alu_out <=
			    (rv1 < rv2) ? 32'b1 : 32'b0; // SLTU
                    	{7'b0000000,3'b100}: alu_out <= rv1 ^ rv2; // XOR
                    	{7'b0000000,3'b101}: alu_out <= rv1 >> rv2[4:0]; // SRL
                    	{7'b0100000,3'b101}: alu_out <= 
			    $signed(rv1) >>> rv2[4:0]; // SRA
                    	{7'b0000000,3'b110}: alu_out <= rv1 | rv2; // OR
                    	{7'b0000000,3'b111}: alu_out <= rv1 & rv2; // AND
           		endcase
            	end
            	7'b0010011: begin // I-type ALU
                		case (funct3)
                    		3'b000: alu_out <= rv1 + imm_i; // ADDI
                    		3'b010: alu_out <= 
					($signed(rv1) < $signed(imm_i)) 
		    			? 32'b1 : 32'b0; // SLTI
                    		3'b011: alu_out <= (rv1 < imm_i) 
					? 32'b1 : 32'b0; // SLTIU
                    		3'b100: alu_out <= rv1 ^ imm_i; // XORI
                    		3'b110: alu_out <= rv1 | imm_i; // ORI
                    		3'b111: alu_out <= rv1 & imm_i; // ANDI
                    		3'b001: alu_out <= shift16l; // SLLI
                    		3'b101: alu_out <= shift16r; // SRLI/SRAI
                		endcase
            		end
		7'b1100011: begin 
				// Branch
			end
		7'b0100011: begin
				O_dmem_addr <= rv1 + imm_s;
				dmem_addr_ex <= rv1 + imm_s;
				if (funct3 == 4'b000) begin
					O_dmem_wmask <= 4'b0001; // SB
				end else if (funct3  == 4'b001) begin
					O_dmem_wmask <= 4'b0011; // SH
				end else begin
					O_dmem_wmask <= 4'b1111; // SW
				end
				O_dmem_wdata <= rv2;
				O_dmem_we <= 1;
			end 
		7'b0000011: begin // LW
				dmem_addr_ex <= rv1 + imm_i;
				O_dmem_addr <= rv1 + imm_i;
				O_dmem_wdata <= 32'h0;
				O_dmem_wmask <= 4'b1111;
				O_dmem_rd <= 1;
			end
		default: begin
			end
        	endcase
		opcode_ex <= opcode;
	end
	rd_ex <= rd;
	imm_u_ex <= imm_u;
	pc_ex <= pc_id;
	funct3_ex <= funct3;
end

// stage 4: MEM memory access and some stage 5: write back to registers
reg [31:0] dmem_rdata;
reg [6:0]  opcode_mem;
reg [4:0]  rd_mem;
//reg [31:0] imm_u_mem;
//reg [31:0] pc_mem;
//reg [31:0] alu_out_mem;

// FIXME for sorting bytes in unaligned LW/LH memory access (this should be 
// in cache.v but it dosent compile with yosys...)
reg [31:0] rdata[4];
reg [1:0] rdatai;
always @* begin
	rdata[0] <= I_dmem_rdata;
	rdata[1] <= {I_dmem_rdata[7:0],I_dmem_rdata[31:8]};
	rdata[2] <= {I_dmem_rdata[15:0],I_dmem_rdata[31:16]};
	rdata[3] <= {I_dmem_rdata[23:0],I_dmem_rdata[31:24]};
	rdatai <= dmem_addr_ex[1:0];
end

always @(posedge I_clk) begin
        if (I_rst) begin
		dmem_rdata <= 32'h0;
        end else if (stall) begin
	end else begin
		case (opcode_ex)
		// Stage 4:
		7'b0000011: begin // Load
			case (funct3_ex)
			3'b000: dmem_rdata <= // LB 
				{{24{rdata[rdatai][7]}}, rdata[rdatai][7:0]}; 
			3'b100: dmem_rdata <= // LBU 
				{24'h0, rdata[rdatai][7:0]}; 
			3'b001: dmem_rdata <= // LH 
				{{16{rdata[rdatai][15]}}, rdata[rdatai][15:0]}; 
			3'b101: dmem_rdata <= // LHU 
				{16'h0, rdata[rdatai][15:0]}; 
			3'b010: dmem_rdata <= rdata[rdatai]; // LW
			default: dmem_rdata <= 32'h0;
			endcase
			end 
		// Stage 5: Write back
        	7'b0110011: regfile[rd_ex] <= alu_out; // R-type
        	7'b0010011: regfile[rd_ex] <= alu_out; // I-type ALU
		7'b1101111: regfile[rd_ex] <= pc_ex + 4; //JAL
		7'b1100111: regfile[rd_ex] <= pc_ex + 4; //JALR
        	7'b0110111: regfile[rd_ex] <= imm_u_ex; // LUI
        	7'b0010111: regfile[rd_ex] <= pc_ex + imm_u_ex; // AUIPC
		default: dmem_rdata <= 32'h0;
		endcase
	end
	opcode_mem <= opcode_ex;
	rd_mem <= rd_ex;
	//imm_u_mem <= imm_u_ex;
	//pc_mem <= pc_ex;
	//alu_out_mem <= alu_out;
end

// stage 5: WB write back
always @(posedge I_clk) begin
        if (I_rst) begin
        end else if (stall) begin
	end else begin 
		case (opcode_mem)
        	//7'b0110011: regfile[rd_mem] <= alu_out_mem; // R-type
        	//7'b0010011: regfile[rd_mem] <= alu_out_mem; // I-type ALU
		7'b0000011: begin
				regfile[rd_mem] <= dmem_rdata; // Loads
			end
		//7'b1101111: regfile[rd_mem] <= pc_mem + 4; //JAL
		//7'b1100111: regfile[rd_mem] <= pc_mem + 4; //JALR
        	//7'b0110111: regfile[rd_mem] <= imm_u_mem; // LUI
        	//7'b0010111: regfile[rd_mem] <= pc_mem + imm_u_mem; // AUIPC
		endcase
	end
end

endmodule

