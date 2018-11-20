# Instruction Selection

### Nick Flanders and Chenyang Eric Liu

Our Codegen module exposes a single curried function to produce assembler
instructions from a given frame and Tree expression. Our munchArgs function
handles function calls with more than 4 arguments by first using the $a0
through $a3 registers and then by adding the remaining arguments to the
frame in reverse order as dictated by the MIPS calling convention.

We have extended our MipsFrame implementation to make the necessary
associations between actual MIPS registers and the temps which will represent
them. In addition to the lists of caller-saves, callee-saves, special
registers, and argument registers, we have defined explicit references to the
return address and stack pointer registers as these are needed for the temp
lists which will be used during liveness analysis.

A Tiger implementation of a factorial function and the corresponding assembler
representation are located in the examples directory.