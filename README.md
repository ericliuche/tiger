# Integration

### Nick Flanders and Chenyang Eric Liu

We added the following components to enable an end-to-end compilation of a Tiger source file:

- Added support for `Frame.stringFrag` to generate assembler for a string
- Updated our frame representation with fields to track moves required for the view shift and the maximum number of outgoing parameters within a frame
- Logic to generate the view shift moves when creating a new frame
- Logic within `procEntryExit1` to save all calleesaves registers to new temps in the prologue and to restore them in the epilogue
- Logic to save/load the return addrees appropriately
- `procEntryExit2` now determines the maximum number of outgoing params and stores this value on the frame
- `procEntryExit3` now appropriately decrements and increments the frame and stack pointers
- Separate handling for string and proc fragments to correctly generate `.data` and `.text` sections in the resulting assembler
- When translating the main procedure, we add a MIPS syscall at the end to print the result to the console

We have submitted a Tiger implementation of a factorial function along with the assembler that
our compiler produces. The factorial program correctly computes and prints the result of 7!.

We have also fixed the behavior of our register allocator as we identified an issue where we would
attempt to simplify precolored nodes.