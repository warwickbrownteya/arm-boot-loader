/* Linker script for ARM Versatile Express A15 bootloader */
/* QEMU vexpress-a15: loads -kernel at DRAM + 0x10000 = 0x80010000 */

ENTRY(_start)

SECTIONS
{
    . = 0x80010000; /* QEMU loads kernel at this offset from DRAM base */

    .text : {
        start.o(.text*)       /* Entry point must be first */
        *(.text*)
    }
    _start = 0x80010000;

    .rodata : {
        *(.rodata*)
    }

    .data : {
        *(.data*)
    }

    /* BSS section - align before and after for clear_bss loop */
    . = ALIGN(4);
    __bss_start = .;
    .bss : {
        *(.bss*)
    }
    . = ALIGN(4);
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
