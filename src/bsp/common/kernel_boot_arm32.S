/*
 * ARM32 Kernel Boot Assembly
 * Unified implementation for ARMv7-A platforms
 *
 * ARM32 Boot Protocol (with DTB):
 *   r0 = 0 (unused)
 *   r1 = 0xFFFFFFFF (indicates DTB boot, not ATAG)
 *   r2 = physical address of DTB
 */

.section .text

/* ============================================================
 * kernel_boot - Jump to Linux kernel
 * Input:  r0 = kernel address
 *         r1 = DTB address (or 0)
 * Does not return
 * ============================================================ */
.global kernel_boot
.type kernel_boot, %function
kernel_boot:
    /* Save kernel address for later branch */
    mov     r4, r0              /* r4 = kernel address */
    mov     r5, r1              /* r5 = DTB address */

    /* Disable interrupts */
    cpsid   if

    /* Disable MMU, caches */
    mrc     p15, 0, r0, c1, c0, 0
    bic     r0, r0, #0x0001     /* Clear M bit (MMU) */
    bic     r0, r0, #0x0004     /* Clear C bit (D-cache) */
    bic     r0, r0, #0x1000     /* Clear I bit (I-cache) */
    mcr     p15, 0, r0, c1, c0, 0
    isb

    /* Invalidate I-cache */
    mov     r0, #0
    mcr     p15, 0, r0, c7, c5, 0   /* ICIALLU */

    /* Invalidate D-cache */
    mov     r0, #0
    mcr     p15, 0, r0, c7, c6, 0   /* DCISW */

    /* Data and instruction synchronization */
    dsb
    isb

    /* Set up ARM32 boot protocol registers:
     * r0 = 0
     * r1 = 0xFFFFFFFF for DTB boot (or machine type for ATAG)
     * r2 = DTB address
     */
    mov     r0, #0

    /* Check if DTB is provided */
    cmp     r5, #0
    moveq   r1, #0              /* No DTB: r1 = 0, r2 = 0 */
    moveq   r2, #0
    mvnne   r1, #0              /* DTB provided: r1 = 0xFFFFFFFF */
    movne   r2, r5              /* r2 = DTB address */

    /* Jump to kernel entry point */
    bx      r4

/* Infinite loop - should never reach here */
.Lhang:
    wfe
    b       .Lhang

/* ============================================================
 * kernel_validate - Check if valid ARM32 zImage
 * Input:  r0 = address to check
 * Output: r0 = 0 if valid, -1 if invalid
 * ============================================================ */
.global kernel_validate
.type kernel_validate, %function
kernel_validate:
    /* Load magic at offset 0x24 */
    ldr     r1, [r0, #0x24]

    /* Compare with zImage magic 0x016F2818 */
    ldr     r2, =0x016F2818
    cmp     r1, r2
    bne     .Lkernel_invalid

    /* Valid kernel */
    mov     r0, #0
    bx      lr

.Lkernel_invalid:
    mvn     r0, #0              /* Return -1 */
    bx      lr

/* ============================================================
 * dtb_validate - Check if valid DTB
 * Input:  r0 = address to check
 * Output: r0 = 0 if valid, -1 if invalid
 * ============================================================ */
.global dtb_validate
.type dtb_validate, %function
dtb_validate:
    /* Load first 4 bytes (magic) */
    ldr     r1, [r0]

    /* DTB magic: 0xD00DFEED big-endian = 0xEDFE0DD0 little-endian */
    ldr     r2, =0xEDFE0DD0
    cmp     r1, r2
    bne     .Ldtb_invalid

    /* Valid DTB */
    mov     r0, #0
    bx      lr

.Ldtb_invalid:
    mvn     r0, #0              /* Return -1 */
    bx      lr

/* ============================================================
 * dtb_get_size - Get DTB total size
 * Input:  r0 = DTB address
 * Output: r0 = size in bytes (big-endian converted)
 * ============================================================ */
.global dtb_get_size
.type dtb_get_size, %function
dtb_get_size:
    /* Load totalsize field at offset 4 */
    ldr     r0, [r0, #4]

    /* Byte swap: big-endian to little-endian */
    rev     r0, r0

    bx      lr

.end
