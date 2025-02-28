# RV32E Emulator
An executor library for RISC-V (`rv32e` variant) machine code.

See the `examples` folder for example usage.

# Instability
Note that this project was created for the sake of learning RISC-V. It is likely to go through multiple breaking API changes, and emulation bugs are more likely than not to emerge. This project should not be relied upon for any serious applications.

# Running Programs
Compiling this as a binary will compile an emulator program that takes in a program file as an argument.

The execution environment is incredibly generous, mapping the entire 32-bit address space to R/W memory.

On startup, the registers (including the program counter) and memory are zeroed. After, the program is loaded into memory, starting at address 0. The stack pointer is then set to the length of the program, plus 0x10000 (this is planned to be configurable).

After this, the emulation begins, stepping through the program as a regular `rv32e` CPU would, until an `ebreak` is met, at which point emulation will stop. This means that, at least for now, programs should use an `ebreak` at the end of their `main` function instead of returning.

Extremely simple terminal I/O is implemented with `ecall`s. When performing an `ecall`, the value stored in `a5` represents the function the environment will execute, with `a0`-`a4` containing the arguments, and `a0` containing the return value. `a0` is *not* clobbered for `void` `ecall`s.

The following `a5` codes are implemented: 
- 0 (`void putchar(uint8_t)`): Write one byte to stdout (and flush stdout)
- 1 (`uint8_t getch()`): Wait for one character to be entered into the terminal (implemented with the `getch` crate, likely to change)

# Compiling C
C code can be compiled for this emulator with the proper setup. Here's how I setup Clang and LLD:
- Along with configuring Clang for `rv32e`, I used `-ffunction-sections` and output to an object file.
- I used LLD with `-oformat=binary`, and a linker script that is setup to place the `.text.main` section before any other section, ensuring that it appears at the very beginning of the file.
With this setup, LLD *should* produce a binary file that the emulator *should* be able to execute.