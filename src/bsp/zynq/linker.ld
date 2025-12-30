/* Linker script for Xilinx Zynq UltraScale+ bootloader */

ENTRY(_start)

SECTIONS
{
    . = 0x00000000; /* Load at start of DDR */

    .text : {
        start.o(.text*)       /* Entry point must be first */
        *(.text*)
    }
    _start = 0x00000000;

    .rodata : {
        *(.rodata*)
    }

    .data : {
        *(.data*)
    }

    /* BSS section - align before and after for clear_bss loop */
    . = ALIGN(8);
    __bss_start = .;
    .bss : {
        *(.bss*)
    }
    . = ALIGN(8);
    __bss_end = .;

    /* Heap starts here - after BSS, before stack */
    __heap_start = .;
    . += 0x10000; /* 64KB heap */
    __heap_end = .;

    . = ALIGN(8);
    . += 0x4000; /* 16KB stack space */

    _end = .;
    stack_top = .;
}
