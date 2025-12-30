/* Linker script for Raspberry Pi bootloader */

ENTRY(_start)

SECTIONS
{
    . = 0x80000; /* Load address for bootloader */

    .text : {
        start.o(.text*)       /* Entry point must be first */
        *(.text*)
    }
    _start = 0x80000;

    .rodata : {
        *(.rodata*)
    }

    .data : {
        *(.data*)
    }

    __bss_start = .;
    .bss : {
        *(.bss*)
    }
    __bss_end = .;

    . = ALIGN(8);

    /* Heap starts here - after BSS, before stack */
    __heap_start = .;
    . += 0x10000; /* 64KB heap */
    __heap_end = .;

    . = ALIGN(8);
    . += 0x2000; /* 8KB stack space */

    _end = .;
    stack_top = .;
}