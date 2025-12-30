/* Linker Script for ARM SBSA Reference Platform Bootloader */

/*
 * MEMORY ADDRESS CONFIGURATION
 * ============================
 * RAM Base:    0x40000000 (1GB)
 * RAM Size:    Up to 8GB supported
 * Bootloader:  64MB region at RAM base
 *
 * WHY NOT 1TB (QEMU sbsa-ref default)?
 * ------------------------------------
 * QEMU's sbsa-ref places RAM at 0x10000000000 (1TB), but this causes
 * AArch64 GOT (Global Offset Table) relocation failures:
 *
 *   Problem: ADRP instruction has ~4GB PC-relative range
 *   Effect:  String literal lookups via GOT corrupt at 1TB
 *   Tried:   -mcmodel=large, PC-relative adr - partial fixes only
 *
 * SOLUTION: Place bootloader at 0x40000000 (within 4GB)
 *   - Compatible with QEMU 'virt' machine RAM layout
 *   - Below 4GB threshold for reliable GOT operations
 *   - Supports systems with up to 8GB RAM
 *   - Peripherals typically mapped below 0x40000000
 *
 * QEMU command:
 *   qemu-system-aarch64 -M virt -cpu cortex-a57 -m 4G -nographic \
 *     -kernel bootloader-sbsa.elf
 */

ENTRY(_start)

MEMORY
{
    /* RAM at 1GB, bootloader uses first 64MB */
    RAM (rwx) : ORIGIN = 0x40000000, LENGTH = 64M
}

SECTIONS
{
    /* Code section */
    .text : {
        *(.text._start)    /* Entry point first */
        *(.text*)
        *(.rodata*)
    } > RAM

    /* Read-only data */
    .rodata : {
        *(.rodata*)
    } > RAM

    /* Initialized data */
    .data : {
        *(.data*)
    } > RAM

    /* BSS section - align before and after for clear_bss loop */
    . = ALIGN(8);
    __bss_start = .;
    .bss : {
        *(.bss*)
        *(COMMON)
    } > RAM
    . = ALIGN(8);
    __bss_end = .;

    /* Stack - 16KB growing down from 80KB mark
     * Stack grows downward, so stack_top is at the high address.
     * We reserve 64KB-80KB for stack (16KB total).
     */
    . = ORIGIN(RAM) + 80K;
    stack_top = .;

    /* Heap - after stack region */
    . = ORIGIN(RAM) + 128K;
    __heap_start = .;
    . = ORIGIN(RAM) + 1M;
    __heap_end = .;

    /* Discard unwanted sections */
    /DISCARD/ : {
        *(.comment)
        *(.note*)
        *(.eh_frame*)
        *(.ARM.exidx*)
        *(.ARM.extab*)
    }
}
