/* Linker script for QEMU Virt Machine bootloader */

ENTRY(_start)

SECTIONS
{
    . = 0x40000000; /* QEMU Virt RAM starts here */

    .text : {
        start.o(.text*)       /* Entry point must be first */
        *(.text*)
    }
    _start = 0x40000000;

    .rodata : {
        *(.rodata*)
    }

    .data : {
        *(.data*)
    }

    /* Align BSS to 8 bytes - critical for clear_bss loop */
    . = ALIGN(8);
    __bss_start = .;
    .bss : {
        *(.bss*)
    }
    . = ALIGN(8);
    __bss_end = .;

    . = ALIGN(8);

    /* Heap starts here - after BSS, before stack */
    __heap_start = .;
    . += 0x10000; /* 64KB heap */
    __heap_end = .;

    . = ALIGN(8);
    . += 0x4000; /* 16KB stack space */

    _end = .;
    stack_top = .;
}
