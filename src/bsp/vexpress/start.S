/* ARM32 Entry Point for Versatile Express A15 (ARMv7-A) */

.section .text._start
.global _start

_start:
    /* Disable interrupts */
    cpsid if

    /* Read current mode */
    mrs r0, cpsr
    and r0, r0, #0x1F

    /* Check if in HYP mode (0x1A) */
    cmp r0, #0x1A
    beq drop_from_hyp

    /* Check if in SVC mode (0x13) */
    cmp r0, #0x13
    beq setup_stack

    /* Switch to SVC mode */
    cps #0x13
    b setup_stack

drop_from_hyp:
    /* Return to SVC mode from HYP mode */
    mrs r0, cpsr
    bic r0, r0, #0x1F
    orr r0, r0, #0x13       /* SVC mode */
    orr r0, r0, #0xC0       /* Disable IRQ/FIQ */
    msr spsr_hyp, r0
    ldr r0, =setup_stack
    msr elr_hyp, r0
    eret

setup_stack:
    /* Set up stack pointer */
    ldr sp, =stack_top

    /* Clear BSS section */
    ldr r0, =__bss_start
    ldr r1, =__bss_end
    mov r2, #0
clear_bss:
    cmp r0, r1
    bge bss_done
    str r2, [r0], #4
    b clear_bss

bss_done:
    /* Jump to C main */
    bl main

    /* Halt if main returns */
halt:
    wfe
    b halt
