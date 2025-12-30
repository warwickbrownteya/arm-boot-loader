/*
 * ARM Bootloader - Raspberry Pi 3 Startup
 * Entry point at 0x80000 (set by GPU firmware)
 *
 * The GPU loads kernel8.img (or kernel7.img for 32-bit)
 * and releases the ARM cores with PC = 0x80000
 */

.section .text._start
.global _start
.type _start, @function

_start:
    /* Check if we are core 0 */
    mrs     x0, mpidr_el1
    and     x0, x0, #3
    cbnz    x0, .Lhang      /* Hang if not core 0 */

    /* Set up stack pointer */
    /* Stack at 0x80000, growing down (code starts at 0x80000) */
    /* Put stack at 0x7F000 (below entry point) */
    ldr     x0, =_stack_top
    mov     sp, x0

    /* Clear BSS */
    ldr     x0, =_bss_start
    ldr     x1, =_bss_end
    cmp     x0, x1
    b.ge    .Lskip_bss
.Lclear_bss:
    str     xzr, [x0], #8
    cmp     x0, x1
    b.lt    .Lclear_bss
.Lskip_bss:

    /* Jump to main */
    bl      main

    /* If main returns, hang */
.Lhang:
    wfe
    b       .Lhang

.size _start, . - _start
