#!/usr/bin/python3



from collections import namedtuple
import re
import argparse

# Some helpful constant values that we'll be using.
Constants = namedtuple("Constants",["NUM_REGS", "MEM_SIZE", "REG_SIZE"])
constants = Constants(NUM_REGS = 8,
                      MEM_SIZE = 2**13,
                      REG_SIZE = 2**16)

def load_machine_code(machine_code, mem):
    """
    Loads an E20 machine code file into the list
    provided by mem. We assume that mem is
    large enough to hold the values in the machine
    code file.
    sig: list(str) -> list(int) -> NoneType
    """
    machine_code_re = re.compile("^ram\[(\d+)\] = 16'b(\d+);.*$")
    expectedaddr = 0
    for line in machine_code:
        match = machine_code_re.match(line)
        if not match:
            raise ValueError("Can't parse line: %s" % line)
        addr, instr = match.groups()
        addr = int(addr,10)
        instr = int(instr,2)
        if addr != expectedaddr:
            raise ValueError("Memory addresses encountered out of sequence: %s" % addr)
        if addr >= len(mem):
            raise ValueError("Program too big for memory")
        expectedaddr += 1
        mem[addr] = instr

def print_state(pc, regs, memory, memquantity):

    """
    Prints the current state of the simulator, including
    the current program counter, the current register values,
    and the first memquantity elements of memory.
    sig: int -> list(int) -> list(int) - int -> NoneType
    """
    print("Final state:")
    print("\tpc="+format(pc,"5d"))
    for reg, regval in enumerate(regs):
        print(("\t$%s=" % reg)+format(regval,"5d"))
    line = ""
    for count in range(memquantity):
        line += format(memory[count], "04x")+ " "
        if count % 8 == 7:
            print(line)
            line = ""
    if line != "":
        print(line)

def revealTrueimm7(imm7):
    """
    the imm7's binary is signed but in imm7 Python variable, it's always saved as a positive decimal value
    this function reveals its "true" decimal value <--- take imm7's sign into consideration
    sig: int --> int
    """
    if((0 <= imm7) and (imm7 <= 63)): # means imm7 in binary is 0000000 to 0111111 <--> imm7's MSB is 0  <--> imm7 is positive --> return imm7 as is
        return imm7
    else: # imm7 >= 64 <--> means imm7 in binary is 1000000 to 1111111 <--> imm7 in binary's MSB is 1 <--> imm7 is negative 
          # --> we get its true decimal value by grabbing from the LSB up to the (n-1)th bit and then subtract the nth bit
        return (imm7 & 63) - 64     # &63 grabs from LSB up to the (n-1)th bit
                                    # -64 is subtracting the nth bit
def revealTrueRelimm(relimm):
    """
    reveal the "true" decimal value of the relimm7 that's passed in
    sig: int --> int
    """
    if((0 <= relimm) and (relimm <= 63)):
        return relimm
    else:
        return (relimm & 32767) - 32768 # grab from LSB up to idx14
                                        # minus off idx15
def signExtend(imm7):
    """
    the imm7 argument is signed
    this function will extend imm7 to 16-bits using 1s if imm7's MSB is 1 
    this function will extend imm7 to 16-bits using 0s if imm7's MSB is 0 === do nothing if imm7's MSB is 0 
    sig: int --> int
    """

    if( (0 <= imm7) and (imm7 <= 63)): # means imm7 in binary is 0000000 to 0111111 <--> imm7's MSB is 0 <--> imm7 is positive --> sign extend by zero-extending --> return imm7 as is
        return imm7
    else: # means imm7 in binary is 1000000 to 1111111 <--> imm7's MSB is 1 <---> imm7 is negative --> sign-extend by extending with 1's
        return (imm7 | 65408)   # our mask should have idx7 to idx15 as 1s and idx0 to idx6 as 0
                                # we should operate with OR so idx7 through idx15 get turned on to 1
def getMemoryAddress(pc):
    """
    This function will check if the memory cell address is within the available memory cells 0 through 8191
    If yes --> no modifications are needed for the address
    If no --> modifications are needed for the address
    sig: int --> int
    """
    if((0 <= pc) and (pc <= 8191)): # address is within the available 0 to 8191 memory cell addresses
        return pc # address is valid as is --> no need to modify address --> return address as is
    else: # address is either overflowed or underflowed --> handle both cases in the same manner
          # we want pc to wrap around to the other side of the range
        return (pc % 8192) # mod to handle wrapping
def simulation(pc, registers, memory):
    """
    This function runs the simulation of E20
    sig: int, list, list --> int
    """

    """ obtain the first line of instructions at pc == 0 aka memory cell 0 """
    instructions = memory[pc]     # pc == 0
                                  # instructions are the contents of each memory cell
    opcode = (instructions & 57344) >> 13    # want to capture bits 15 14 13 to get opcode so we isolate them and then shift
    rA   = (instructions & 7168  )  >> 10       # want to capture bits 12 11 10 to get rA so we isolate them and then shift
    rB   = (instructions & 896 ) >> 7       # want to capture bits 9 8 7 to get rB so we isolate them and then shift
    rC   = (instructions & 112)  >> 4      # want to capture bits 6 5 4 to get rC so isolate them and then shift
    imm13 = instructions & 8191           # isolate bits 12 11 ... 0 to get imm13
    imm7 = instructions &  127            # isolate bits 6 5 4 ... 0 to get imm7
    func = instructions &  15             # isolate bits 3 2 1 0 to get func
                                          # func is used to distinguish between operations that have the same opcode, namely the opcode 000

                                          # in Python, all of these variables are treated as DECIMAL numbers

    """ the core of our simulation """
    while( not (opcode == 2 and imm13 == pc) ):         # while not halt, keep reading, parsing and executing instructions line-by-line (ie cell-by-cell)
                                                        # halt === opcode == 2 in decimal AND jumping in place which means jumping to current pc

        if (opcode == 0): # operations with three register arguments: add, sub, or, and, slt, jr 
                          # we need to further distinguish these operations by their func bits

            if(func == 8): # operation is jr
                pc = registers[rA]
            else: # possible operations are add, sub, or, and, slt
                if (rC == 0): # if we try to modify register0 by storing value in register 0 --> skip this instruction 
                    pass
                else: # our dst register is not $0
                    # obtain the values within our registers
                    srcA_value = registers[rA]
                    srcB_value = registers[rB]
                    if(func == 0): # operation is add
                        sum = srcA_value + srcB_value 
                        if (sum > 65535): # 65535 is the largest decimal number that the 16-bit register can hold            
                            sum = (sum & 65535)  # handling overflow --> we need to wrap around to other end of the 16-bit range
                        registers[rC] = sum
                    elif (func == 1): # operation is sub
                        difference = srcA_value - srcB_value
                        if (difference < 0): # handling underflow --> we need to wrap around to other end of the 16-bit range
                            difference = (difference & 65535) 
                        registers[rC] = difference
                    elif (func == 2): # operation is or
                        registers[rC] = (srcA_value | srcB_value)
                    elif(func== 3): # operation is and
                        registers[rC] = (srcA_value & srcB_value)
                    else: # operation is slt
                        if (srcA_value < srcB_value): # comparison is done unsigned
                            registers[rC] = 1
                        else:
                            registers[rC] = 0
                pc = pc + 1 # these instructions proceed pc forward by 1

        # operations for two register arguments 
        elif(opcode == 7): # operation is slti
            if(rB == 0): # if we try to modify register0 by storing value in register 0 --> skip the instruction
                pass
            else: # we're not trying to modify register0
                srcA_value = registers[rA]
                imm7 = signExtend(imm7) # imm7 is sign-extended as per manual
                if(srcA_value < imm7): # comparison is done unsigned
                    registers[rB] = 1
                else:
                    registers[rB] = 0
            pc = pc + 1 
        elif(opcode == 4): # operation is load word
            if (rB == 0): # if we try to modify register0 by storing value in register 0 --> skip the instruction
                pass
            else: # we're not trying to modify register0
                srcA_value = registers[rA]
                imm7 = revealTrueimm7(imm7)  # imm7 is signed
                memoryIdx = getMemoryAddress(srcA_value + imm7) # we want the contents from this memory address 
                registers[rB] = memory[memoryIdx] # put the contents of the memory address into the destination register
            pc = pc + 1
        elif(opcode == 5): # operation is save word
            srcA_value = registers[rA]
            imm7 = revealTrueimm7(imm7) # imm7 is signed
            memoryIdx = getMemoryAddress(srcA_value + imm7) # this is the memory address we want to place register's value into
            memory[memoryIdx] = registers[rB] # put the value of registerB into the cell of target memory address
            pc = pc + 1
        elif(opcode == 6): # operation is jeq
            srcA_value = registers[rA]
            srcB_value = registers[rB]
            if(srcA_value == srcB_value): # srcA_value == srcB_value --> we should jump
                
                pc = revealTrueRelimm(signExtend(imm7)) + pc + 1    # when a jump is performed --> rel_imm is sign extended and added to the successor value of the program counter
                                                                                        # rel_imm is the 7bits we grabbed from instructions
                                                                                        # successor value of the program counter is pc+1
                                                                                        # imm7 is signed
            
            else: # srcA_value =/= srcB_value
                pc = pc + 1
        elif(opcode == 1): # operation is addi
            if (rB == 0): # if we try to modify register0 by storing value in register 0 --> skip the instruction
                pass
            else: # we're not trying to modify register0
                srcA_value = registers[rA]
                imm7 = revealTrueimm7(imm7) # imm7 is signed
                sum = srcA_value + imm7
                if((sum > 65535) or (sum < 0)): # handle overflow / underflow of the sum
                                                # sum can be negative if we add a negative immediate value
                    sum = (sum & 65535)
                registers[rB] = sum
            pc = pc + 1
        # operations with no register arguments 
        elif (opcode == 2): # operation is j 
            pc = imm13 # jump to the given immediate value address
        elif(opcode == 3): # operation is jal
            registers[7] = pc + 1 # put the address of the subsequent instruction (aka memory cell) into register7
                                                 # this saved address must be adjusted 
            pc = imm13 # jump to the given immediate value address
        else: # if the machine code has invalid / undefined instructions then we ignore
            pc = pc+1
                
        # obtain the next line (aka next cell) of instructions
        instructions = memory[getMemoryAddress(pc)]
        opcode = (instructions & 57344) >> 13    # want to capture bits 15 14 13 to get opcode so we isolate them and then shift
        rA   = (instructions & 7168  )  >> 10       # want to capture bits 12 11 10 to get rA so we isolate them and then shift
        rB   = (instructions & 896 ) >> 7       # want to capture bits 9 8 7 to get rB so we isolate them and then shift
        rC   = (instructions & 112)  >> 4      # want to capture bits 6 5 4 to get rC so we isolate them and then shift
        imm13 = (instructions & 8191)         # isolate bits 12 11 ... 0 to get imm13
        imm7 = (instructions &  127)          # isolate bits 6 5 4 ... 0 to get imm7
        func = (instructions &  15)           # isolate bits 3 2 1 0 to get func
                                              # func is used to distinguish between operations that have the same opcode, namely the opcode 000

                                              # in Python, all of these variables are treated as DECIMAL numbers

    # out of while loop means we've reached halt === our E20 program has concluded --> componenents (pc, registers, memory) should be updated
    return pc

def main():

    parser = argparse.ArgumentParser(description='Simulate E20 machine')
    parser.add_argument('filename', help='The file containing machine code, typically with .bin suffix')
    cmdline = parser.parse_args()


    """ initial states of our simulator """
    pc = 0
    registers = []
    for i in range(8): # initialize all 8 registers to 0
        registers.append(0)
    memory = []
    for i in range(8192): # initialize all 8192 memory cells to 0
        memory.append(0)
    

    with open(cmdline.filename) as file:
        pass # TODO: your code here. Load file and parse using load_machine_code
        load_machine_code (file, memory)

    # TODO: your code here. Do simulation.
    pc = simulation(pc, registers, memory)                           # input pc (an int), register (a list) and memory (a list) into simulation function
                                                                     # our simulation function needs to update the three components of E20 process
                                                                    
                                                                    # we let our simulation mutate our two lists registers and memory
                                                                    # but we want to return pc to indicate updated program counter
                                                                        # pc is int and ints are immutable so our simulation function will not update pc unless we return its updated value
                                                    
    # TODO: your code here. print the final state of the simulator before ending, using print_state
    print_state(pc, registers, memory, 128) # input the updated components into given print function to display the updates
                                            # we only want to show memory cells 0, 1, 2, ..., 127

if __name__ == "__main__":
    main()
#ra0Eequ6ucie6Jei0koh6phishohm9
