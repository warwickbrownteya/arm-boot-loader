/* Raspberry Pi Bootloader Entry Point */

.global _start
_start:
    /* Disable interrupts immediately */
    MSR DAIFSET, #0xF

    /* SMP: Only run on CPU 0, park other CPUs immediately
     * This must happen FIRST before any memory access to avoid
     * race conditions with multiple cores */
    MRS X0, MPIDR_EL1
    AND X0, X0, #0xFF    /* Get CPU ID (Affinity Level 0) */
    CBNZ X0, secondary_halt

    /* Set up stack pointer (CPU 0 only) */
    LDR X1, =stack_top
    MOV SP, X1

    /* Clear BSS */
    LDR X0, =__bss_start
    LDR X1, =__bss_end
    MOV X2, #0
clear_bss:
    CMP X0, X1
    B.EQ clear_bss_done
    STRB W2, [X0], #1  /* Store 1 byte at a time to avoid overflow */
    B clear_bss

clear_bss_done:
    /* Jump to main */
    BL main

    /* Should not return */
hang:
    WFI
    B hang

/* Secondary CPUs wait here in low-power state */
secondary_halt:
    WFE                  /* Wait for event */
    B secondary_halt     /* Loop forever */

/* Exception vectors (minimal) */
.global exception_vector
exception_vector:
    B hang  /* Synchronous */
    B hang  /* IRQ */
    B hang  /* FIQ */
    B hang  /* SError */
