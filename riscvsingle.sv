// COMPILE: iverilog.exe -g2012 -o riscvsingle.vcd -tvvp .\riscvsingle.sv
// SIMULATE: vvp .\riscvsingle.vcd
// Simulador online: https://www.edaplayground.com/ 


// Módulo de testes
module testbench();

  logic        clk; // Sinal de clock
  logic        reset; // Sinnal de reset
  
  //WriteData e DataAdr tem tamanho de 32 bits (tamanho de uma "word" em RISCV).

  logic [31:0] WriteData;
  logic [31:0] DataAdr; 
  logic        MemWrite;

  // Módulo mais "alto nível"
  top dut(clk, reset, WriteData, DataAdr, MemWrite); // Instanciando o módulo "top" com nome de instancia "dut" (devide under test).
  
  // initialize test
  initial
    begin
      reset <= 1; # 22; reset <= 0; // Ativa o reset, espera 22 u.t. e depois desliga o reset.
    end

  // generate clock to sequence tests
  always
    begin
      clk <= 1; # 5; clk <= 0; # 5; //Período de 10 unidades de tempo (5 u.t. com clk = 1, 5 u.t. com clock = 0)
    end

  // check results
  always @(negedge clk) // Prestar atenção, pois é sensível a borda negativa (negedge)
    begin
      if(MemWrite) begin
        if(DataAdr === 100 & WriteData === 25) begin
          $display("Simulation succeeded");
          $stop;
        end else if (DataAdr !== 96) begin
          $display("Simulation failed");
          $stop;
        end
      end
    end
endmodule

//Módulo inicial, conecta os módulos riscsingle, imem e dmem
module top(input  logic        clk, reset, 
           output logic [31:0] WriteData, //valor que será escrito em dmem (data memory) em operações de sw (store word)
           output logic [31:0] DataAdr, // Endereço de memória (base + offset) calculado pela ALU 
           output logic        MemWrite); // Controle de desvio condicional (em caso de beq, jal), caso seja 0, PC segue normalmente (PC+4)

  logic [31:0] Instr, ReadData;
  logic [31:0] PC; // Guarda o endereço da próxima instrução
  
  // instancia o processador (rvsingle), instruction memory (imem) e data memory(dmem)
  riscvsingle rvsingle(clk, reset, PC, Instr, MemWrite, DataAdr, // OBSERVAR QUE: Quando instanciado, DataAdr vai com nomes diferentes para os módulos, mas fora desse contexto ele é chamado de DataAdr (no testbench) 
                     WriteData, ReadData, PCSrc); //Modificação: Add PCSrc na instanciação do módulo riscvsingle                
  imem imem(PC, Instr);
  dmem dmem(clk, MemWrite, DataAdr, WriteData, ReadData);
endmodule

// Principal módulo, conecta o controle e o caminho de dados
module riscvsingle(input  logic        clk, reset,
                  output logic [31:0] PC, //(Saída) Program Counter: Instruão atual do pc (aquelas em riscV)
                  input  logic [31:0] Instr, //(entrada) Instrução atual do PC, recebe de Imem
                  output logic        MemWrite, // ativa escrita na memória de dados
                  output logic [31:0] ALUResult, // Resultado da ALU
                  output logic [31:0]  WriteData, // Dado a ser escrito na memória
                  input  logic [31:0] ReadData, // Dado lido da memória de dados (input do Data Memory)
                  output logic        PCSrc); // Sinal que decide se haverá salto
                                    // [MODIFICAÇAO] PCSrc nao estava sendo passado //
  logic       ALUSrc; // seleciona entre registrador e imediato como segundo operando da ALU
  logic       RegWrite; // ativa escrita no banco de registradores
  logic       Jump; // instrução de salto
  logic       Zero; // flag da ALU, usada para branch (ex: beq verifica se resultado foi zero)

  logic [1:0] ResultSrc; // Seleciona a origem do dado que será escrito no registrador (ALU, memória, PC+4)
  logic [1:0] ImmSrc; // controla o tipo de extração do valor imediato
  logic [2:0] ALUControl; // Define a operação que será feita na alu (8 opções)

  //instancia controller e datapath
  controller c(Instr[6:0], Instr[14:12], Instr[30], Zero,
               ResultSrc, MemWrite, PCSrc,
               ALUSrc, RegWrite, Jump,
               ImmSrc, ALUControl);
  datapath dp(clk, reset, ResultSrc, PCSrc,
              ALUSrc, RegWrite,
              ImmSrc, ALUControl,
              Zero, PC, Instr,
              ALUResult, WriteData, ReadData);
endmodule

// Com base nos campos de instrução, o controller gera sinais de controle para o datapath, e para a ULA (qual operação realizar)
module controller(input  logic [6:0] op,
                  input  logic [2:0] funct3,
                  input  logic       funct7b5, //  bit 5 do funct7: diferencia operações como add/sub
                  input  logic       Zero,
                  output logic [1:0] ResultSrc, 
                  output logic       MemWrite, 
                  output logic       PCSrc, ALUSrc,
                  output logic       RegWrite, Jump, 
                  output logic [1:0] ImmSrc,
                  output logic [2:0] ALUControl);

  logic [1:0] ALUOp;
  logic       Branch;
  // instancia o main decoder e o alu decoder
  maindec decoder(op, ResultSrc, MemWrite, Branch, ALUSrc, RegWrite, Jump, ImmSrc, ALUOp);
  
  aludec alu_decoder(op[5], funct3, funct7b5, ALUOp, ALUControl);

  assign PCSrc = (Branch & Zero) | Jump;
endmodule

// Gera sinais de controle com base no campo opcode (op) da instrução RISC-V.
// Esses sinais de controle são enviados para o caminho de dados (datapath) para controlar como a instrução será executada.
module maindec(input  logic [6:0] op,
              output logic [1:0] ResultSrc,
              output logic       MemWrite,
              output logic       Branch,
              output logic       ALUSrc,
              output logic       RegWrite, 
              output logic       Jump,
              output logic [1:0] ImmSrc,
              output logic [1:0] ALUOp);

  logic [10:0] controls;

  assign {RegWrite, ImmSrc, ALUSrc, MemWrite,
          ResultSrc, Branch, ALUOp, Jump} = controls;

  always_comb
    case(op)
    // RegWrite_ImmSrc_ALUSrc_MemWrite_ResultSrc_Branch_ALUOp_Jump
      7'b0000011: controls = 11'b1_00_1_0_01_0_00_0; // lw
      7'b0100011: controls = 11'b0_01_1_1_00_0_00_0; // sw
      7'b0110011: controls = 11'b1_xx_0_0_00_0_10_0; // R-type 
      7'b1100011: controls = 11'b0_10_0_0_00_1_01_0; // beq
      7'b0010011: controls = 11'b1_00_1_0_00_0_00_0; // I-type ALU (addi, ori, andi, slti)
      7'b1101111: controls = 11'b1_11_0_0_10_0_00_1; // jal
      default:    controls = 11'bx_xx_x_x_xx_x_xx_x; // non-implemented instruction
    endcase
endmodule

//Gera sinais de controle para a ALU (Unidade Lógica e Aritmética), com base nos campos da instrução
module aludec(input  logic       opb5,
             input  logic [2:0] funct3,
             input  logic       funct7b5,
             input  logic [1:0] ALUOp,
             output logic [2:0] ALUControl); // especifica qual operação a ULA deve realizar.

  logic  RtypeSub;
  assign RtypeSub = funct7b5 & opb5;  // TRUE for R-type subtract instruction

  always_comb
    case(ALUOp)
      2'b00:                ALUControl = 3'b000; // addition
      2'b01:                ALUControl = 3'b001; // subtraction
      default: case(funct3) // R-type or I-type ALU
                 3'b000:  if (RtypeSub) 
                            ALUControl = 3'b001; // sub
                          else          
                            ALUControl = 3'b000; // add, addi
                 3'b010:    ALUControl = 3'b101; // slt, slti
                 3'b110:    ALUControl = 3'b011; // or, ori
                 3'b111:    ALUControl = 3'b010; // and, andi
                 default:   ALUControl = 3'bxxx; // ???
               endcase
    endcase
endmodule

module datapath(input  logic        clk, reset,
               input  logic [1:0]  ResultSrc,
               input  logic        PCSrc,
               input  logic        ALUSrc,
               input  logic        RegWrite,
               input  logic [1:0]  ImmSrc,
               input  logic [2:0]  ALUControl,
               output logic        Zero,
               output logic [31:0] PC,
               input  logic [31:0] Instr,
               output logic [31:0] ALUResult,
               output logic [31:0] WriteData,
               input  logic [31:0] ReadData);

  logic [31:0] PCNext, PCPlus4, PCTarget; // Valores alternativos para o próximo PC
  logic [31:0] ImmExt; // imediato estendido
  logic [31:0] SrcA, SrcB; // Operandos da ALU
  logic [31:0] Result; // valor a ser escrito no registrador

  // PC logic
  flopr #(32) pc_reg(clk, reset, PCNext, PC); // Registrador do PC
  adder       pc_incr(PC, 32'd4, PCPlus4); // PC + 4 (próxima instrução)
  adder       pc_branch(PC, ImmExt, PCTarget); // PC + imediato (desvio)
  mux2 #(32)  pc_mux(PCPlus4, PCTarget, PCSrc, PCNext); // Mux: decide próximo PC


  // Instancia refile e extend
  regfile rf(clk, RegWrite, Instr[19:15], Instr[24:20], Instr[11:7], Result, SrcA, WriteData);
  extend ext(Instr[31:7], ImmSrc, ImmExt);

  // ALU logic
  mux2 #(32) srcbmux(WriteData, ImmExt, ALUSrc, SrcB);
  alu alu(SrcA, SrcB, ALUControl, ALUResult, Zero);
  mux3 #(32) resultmux(ALUResult, ReadData, PCPlus4, ResultSrc, Result);
endmodule

// Banco de registradores
module regfile(input  logic        clk, 
               input  logic        we3, // (recebe o sinal de RegWrite) Write enable 3 - verificação se we3 será 1 ou 0
               input  logic [ 4:0] a1, a2, a3, //  índices dos registradores (5 bits → 32 registradores)
               input  logic [31:0] wd3, // valor a ser escrito em a3, se we3 = 1
               output logic [31:0] rd1, rd2); // saídas que representam os valores lidos de a1 e a2

  logic [31:0] rf[31:0]; // Cria 32 registradores de 32 bits

  always_ff @(posedge clk)
    if (we3) rf[a3] <= wd3; // Na borda de subida do clock, escreve wd3 no registrador a3, se we3 estiver ativo

  assign rd1 = (a1 != 0) ? rf[a1] : 0; // se o registrador for x0, retorna 0. Dúvida: x0 ser 0 é uma convençção, ou regra? REGRA
  assign rd2 = (a2 != 0) ? rf[a2] : 0; // se o registrador for x0, retorna 0 
endmodule

module adder(input  [31:0] a, b,
             output [31:0] y);

  assign y = a + b;
endmodule

// pega os bits do imediato da instrução (em formatos como I, S, B, J) e transforma esse valor em um número de 32 bits com sinal
module extend(input  logic [31:7] instr,
              input  logic [1:0]  immsrc, // Formato de imediato ()
              output logic [31:0] immext);
 
  always_comb
    case(immsrc) 
      2'b00:   immext = {{20{instr[31]}}, instr[31:20]}; // I-type
      2'b01:   immext = {{20{instr[31]}}, instr[31:25], instr[11:7]}; // S-type 
      2'b10:   immext = {{20{instr[31]}}, instr[31], instr[7], instr[30:25], instr[11:8], 1'b0}; // B-type
      2'b11:   immext = {{12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0}; // J-type
      default: immext = 32'bx;
    endcase             
endmodule

// Flipflop com reset padrão
module flopr #(parameter WIDTH = 8)
              (input  logic             clk, reset,
               input  logic [WIDTH-1:0] d, 
               output logic [WIDTH-1:0] q);

  always_ff @(posedge clk, posedge reset)
    if (reset) q <= 0;
    else       q <= d;
endmodule

module mux2 #(parameter WIDTH = 8)
             (input  logic [WIDTH-1:0] d0, d1, 
              input  logic             s, 
              output logic [WIDTH-1:0] y);

  assign y = s ? d1 : d0; 
endmodule

module mux3 #(parameter WIDTH = 8)
             (input  logic [WIDTH-1:0] d0, d1, d2, //entradas
              input  logic [1:0]       s, // seleção
              output logic [WIDTH-1:0] y); // saída

  assign y = s[1] ? d2 : (s[0] ? d1 : d0); 
endmodule

// Módulo no qual o risV se conecta com o HDL
// Recebe "a" de datapath (PC), que é a posição da instrução atual do programa, e devolve a instrução equivalente "rd".
module imem(input  logic [31:0] a,
            output logic [31:0] rd);

  logic [31:0] RAM[63:0]; // Cria a memória interna do nosso processador.
                          // Nesse caso, temos um vetor de 64 words, e cada posição é uma word (instrução) de 32 bits (4 bytes). Totalizando uma memória de 256 bytes
  initial                 // Lembrar que RAM é um vetor de PALAVRAS, ou seja, cada palavra possui 4 bytes. Ou seja, para a próxima instrução, devemos pular 4 bytes.
      $readmemh("riscvtest.txt",RAM,0 , 20); // Carrega os valores de arquivo txt no vetor RAM, de 0 a 20 (nosso código em RISCV possui 21 instruções)

  assign rd = RAM[a[31:2]]; // word aligned, basicamente um shift bit de 2 (divindo assim o número por 4).
endmodule                   // exemplo: Se queremos a segunda instrução, "a" (recebido de PC) será 0x1. Porém 0x1 no nosso vetor RAM é o segundo byte da primeira word,
                            // na verdade nós queremos 0x4 na RAM, por isso dividimos a RAM por 4 (RAM[a >> 2])
module dmem(input  logic        clk, we,
            input  logic [31:0] a, wd,
            output logic [31:0] rd);

  logic [31:0] RAM[63:0];

  assign rd = RAM[a[31:2]]; // word aligned

  always_ff @(posedge clk)
    if (we) RAM[a[31:2]] <= wd;
endmodule

// Famosa ULA, conhecemos bem
module alu(input  logic [31:0] a, b,
           input  logic [2:0]  alucontrol,
           output logic [31:0] result,
           output logic        zero);

  logic [31:0] condinvb, sum;
  logic        v;              // overflow
  logic        isAddSub;       // true when is add or subtract operation

  assign condinvb = alucontrol[0] ? ~b : b; // se alucontrol[0] = 0, então é soma (b normal)
  assign sum = a + condinvb + alucontrol[0]; // se alucontrol[0] = 1, então é subtração (~b + 1), ou seja, soma com complemento de dois.
  assign isAddSub = ~alucontrol[2] & ~alucontrol[1] |
                    ~alucontrol[1] & alucontrol[0]; // Apenas operaçõs com sub ou add podem causar overflow, por isso isAddSub ativa quando alguma
                                                    // operação usa (add, sub, slt)
  always_comb
    case (alucontrol)
      3'b000:  result = sum;         // add
      3'b001:  result = sum;         // subtract
      3'b010:  result = a & b;       // and
      3'b011:  result = a | b;       // or
      3'b100:  result = a ^ b;       // xor
      3'b101:  result = sum[31] ^ v; // slt
      3'b110:  result = a << b[4:0]; // sll
      3'b111:  result = a >> b[4:0]; // srl
      default: result = 32'bx;
    endcase

  assign zero = (result == 32'b0);
  assign v = ~(alucontrol[0] ^ a[31] ^ b[31]) & (a[31] ^ sum[31]) & isAddSub; // detecão de overflow
  
endmodule