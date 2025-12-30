/*
 * ARM64 Kernel Boot Assembly
 * Unified implementation for all AArch64 platforms
 *
 * ARM64 Boot Protocol:
 *   x0 = physical address of device tree blob (DTB)
 *   x1 = 0 (reserved for future use)
 *   x2 = 0 (reserved for future use)
 *   x3 = 0 (reserved for future use)
 */

.section .text

/* ============================================================
 * kernel_boot - Jump to Linux kernel
 * Input:  x0 = kernel address
 *         x1 = DTB address (or 0)
 * Does not return
 * ============================================================ */
.global kernel_boot
.type kernel_boot, %function
kernel_boot:
    /* Save kernel and DTB addresses */
    mov     x4, x0              /* x4 = kernel address */
    mov     x5, x1              /* x5 = DTB address */

    /* Disable interrupts (DAIF = Debug, Async, IRQ, FIQ) */
    msr     daifset, #0xf

    /* Disable MMU, D-cache, I-cache */
    mrs     x0, sctlr_el1
    bic     x0, x0, #(1 << 0)   /* Clear M bit (MMU) */
    bic     x0, x0, #(1 << 2)   /* Clear C bit (D-cache) */
    bic     x0, x0, #(1 << 12)  /* Clear I bit (I-cache) */
    msr     sctlr_el1, x0
    isb

    /* Invalidate I-cache */
    ic      iallu
    dsb     sy
    isb

    /* Set up ARM64 boot protocol registers:
     * x0 = DTB address (primary boot data)
     * x1-x3 = 0 (reserved)
     */
    mov     x0, x5              /* x0 = DTB address */
    mov     x1, xzr             /* x1 = 0 */
    mov     x2, xzr             /* x2 = 0 */
    mov     x3, xzr             /* x3 = 0 */

    /* Jump to kernel entry point */
    br      x4

/* Infinite loop - should never reach here */
.Lhang:
    wfe
    b       .Lhang

/* ============================================================
 * kernel_validate - Check if valid ARM64 kernel image
 * Input:  x0 = address to check
 * Output: x0 = 0 if valid, -1 if invalid
 * ============================================================ */
.global kernel_validate
.type kernel_validate, %function
kernel_validate:
    /* Load magic number at offset 0x38 (56 bytes) */
    ldr     w1, [x0, #0x38]

    /* Compare with ARM64 magic: 0x644d5241 ("ARM\x64") */
    mov     w2, #0x5241
    movk    w2, #0x644d, lsl #16
    cmp     w1, w2
    b.ne    .Lkernel_invalid

    /* Valid kernel */
    mov     x0, #0
    ret

.Lkernel_invalid:
    mov     x0, #-1
    ret

/* ============================================================
 * dtb_validate - Check if valid DTB
 * Input:  x0 = address to check
 * Output: x0 = 0 if valid, -1 if invalid
 * ============================================================ */
.global dtb_validate
.type dtb_validate, %function
dtb_validate:
    /* Load first 4 bytes (magic) */
    ldr     w1, [x0]

    /* DTB magic: 0xD00DFEED big-endian = 0xEDFE0DD0 little-endian */
    mov     w2, #0x0DD0
    movk    w2, #0xEDFE, lsl #16
    cmp     w1, w2
    b.ne    .Ldtb_invalid

    /* Valid DTB */
    mov     x0, #0
    ret

.Ldtb_invalid:
    mov     x0, #-1
    ret

/* ============================================================
 * dtb_get_size - Get DTB total size
 * Input:  x0 = DTB address
 * Output: w0 = size in bytes (big-endian converted)
 * ============================================================ */
.global dtb_get_size
.type dtb_get_size, %function
dtb_get_size:
    /* Load totalsize field at offset 4 */
    ldr     w0, [x0, #4]

    /* Byte swap: big-endian to little-endian */
    rev     w0, w0

    ret

.end
