/* ARM64 Entry Point for Xilinx Zynq UltraScale+ */

.section .text._start
.global _start

_start:
    /* Disable interrupts */
    msr daifset, #0xf

    /* Read current exception level */
    mrs x0, CurrentEL
    lsr x0, x0, #2
    and x0, x0, #3

    /* If EL3, drop to EL1 */
    cmp x0, #3
    b.eq drop_from_el3

    /* If EL2, drop to EL1 */
    cmp x0, #2
    b.eq drop_from_el2

    /* Already at EL1, continue */
    b setup_stack

drop_from_el3:
    /* Configure SCR_EL3 */
    mov x0, #(1 << 10)      /* RW bit - EL2 is AArch64 */
    orr x0, x0, #(1 << 0)   /* NS bit - Non-secure */
    msr scr_el3, x0

    mov x0, #0b01001       /* EL1h mode */
    msr spsr_el3, x0
    adr x0, drop_from_el2
    msr elr_el3, x0
    eret

drop_from_el2:
    /* Enable AArch64 at EL1 */
    mov x0, #(1 << 31)      /* RW bit - EL1 is AArch64 */
    msr hcr_el2, x0

    /* Setup SPSR for EL1 */
    mov x0, #0b00101       /* EL1h mode */
    msr spsr_el2, x0
    adr x0, setup_stack
    msr elr_el2, x0
    eret

setup_stack:
    /* Set up stack pointer */
    ldr x0, =stack_top
    mov sp, x0

    /* Clear BSS section */
    ldr x0, =__bss_start
    ldr x1, =__bss_end
clear_bss:
    cmp x0, x1
    b.ge bss_done
    str xzr, [x0], #8
    b clear_bss

bss_done:
    /* Jump to C main */
    bl main

    /* Halt if main returns */
halt:
    wfe
    b halt
