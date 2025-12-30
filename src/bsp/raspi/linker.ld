/*
 * ARM Bootloader - Raspberry Pi 3 Linker Script
 *
 * Memory layout for BCM2837:
 * - RAM starts at 0x00000000
 * - GPU loads kernel at 0x00080000 (512KB offset)
 * - Stack below entry point (0x0007F000)
 * - Heap after code
 */

ENTRY(_start)

MEMORY
{
    /* RAM below entry point for stack */
    STACK (rw)  : ORIGIN = 0x00070000, LENGTH = 64K

    /* Code region starts at GPU entry point */
    RAM (rwx)   : ORIGIN = 0x00080000, LENGTH = 128K

    /* Heap after code */
    HEAP (rw)   : ORIGIN = 0x000A0000, LENGTH = 64K
}

SECTIONS
{
    /* Code at entry point */
    .text : {
        *(.text._start)
        *(.text*)
        . = ALIGN(8);
    } > RAM

    /* Read-only data */
    .rodata : {
        *(.rodata*)
        . = ALIGN(8);
    } > RAM

    /* Initialized data */
    .data : {
        *(.data*)
        . = ALIGN(8);
    } > RAM

    /* BSS (zero-initialized) - align before and after for clear_bss loop */
    . = ALIGN(8);
    _bss_start = .;
    .bss : {
        *(.bss*)
        *(COMMON)
        . = ALIGN(8);
    } > RAM
    . = ALIGN(8);
    _bss_end = .;

    /* Stack (grows down from top) */
    .stack (NOLOAD) : {
        . = ORIGIN(STACK) + LENGTH(STACK);
        _stack_top = .;
    } > STACK

    /* Heap */
    .heap (NOLOAD) : {
        _heap_start = .;
        __heap_start = .;  /* Alias for boot_common.c */
        . = ORIGIN(HEAP) + LENGTH(HEAP);
        _heap_end = .;
        __heap_end = .;    /* Alias for boot_common.c */
    } > HEAP

    /* Discard unnecessary sections */
    /DISCARD/ : {
        *(.comment)
        *(.note*)
        *(.eh_frame*)
        *(.ARM.*)
    }
}
