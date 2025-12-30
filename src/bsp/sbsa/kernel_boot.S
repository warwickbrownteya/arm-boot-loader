/*
 * ARM Bootloader - Kernel Boot Assembly Routines
 * ARM64 Linux Boot Protocol Implementation
 *
 * ARM64 boot requirements:
 *   - MMU off
 *   - D-cache off (or all RAM clean/invalidated)
 *   - I-cache may be on or off
 *   - x0 = physical address of DTB
 *   - x1-x3 = 0 (reserved)
 *   - CPU in EL2 or EL1 (we're in EL1)
 */

.section .text
.global kernel_boot
.type kernel_boot, @function

/*
 * kernel_boot(uint64_t kernel_addr, uint64_t dtb_addr)
 *   x0 = kernel entry address
 *   x1 = DTB address (will be moved to x0 for kernel)
 */
kernel_boot:
    /* Save kernel address in x4 temporarily */
    mov     x4, x0

    /* Disable interrupts */
    msr     daifset, #0xf

    /* Clean and invalidate data cache */
    /* This is a simplified version - full implementation would
       iterate through all cache levels */

    /* Disable D-cache and I-cache */
    mrs     x0, sctlr_el1
    bic     x0, x0, #(1 << 2)    /* Clear C bit (D-cache) */
    bic     x0, x0, #(1 << 12)   /* Clear I bit (I-cache) */
    msr     sctlr_el1, x0
    isb

    /* Invalidate instruction cache */
    ic      iallu
    isb

    /* Data synchronization barrier */
    dsb     sy
    isb

    /* Set up ARM64 boot protocol registers */
    mov     x0, x1              /* x0 = DTB address */
    mov     x1, xzr             /* x1 = 0 (reserved) */
    mov     x2, xzr             /* x2 = 0 (reserved) */
    mov     x3, xzr             /* x3 = 0 (reserved) */

    /* Jump to kernel - never returns */
    br      x4

.size kernel_boot, . - kernel_boot


.section .text
.global kernel_validate
.type kernel_validate, @function

/*
 * kernel_validate(uint64_t kernel_addr)
 *   x0 = kernel address
 *   Returns: 0 if valid, -1 if invalid
 */
kernel_validate:
    /* Load magic number from offset 0x38 (56 bytes) */
    ldr     w1, [x0, #0x38]

    /* Check for ARM64 magic: 0x644d5241 */
    mov     w2, #0x5241         /* "RA" */
    movk    w2, #0x644d, lsl #16 /* "dM" -> "ARM\x64" */

    cmp     w1, w2
    b.eq    .Lvalid

    /* Invalid magic */
    mov     x0, #-1
    ret

.Lvalid:
    mov     x0, #0
    ret

.size kernel_validate, . - kernel_validate


.section .text
.global dtb_validate
.type dtb_validate, @function

/*
 * dtb_validate(uint64_t dtb_addr)
 *   x0 = DTB address
 *   Returns: 0 if valid, -1 if invalid
 *
 * DTB magic is 0xD00DFEED in big-endian
 * In little-endian memory it appears as 0xEDFE0DD0
 */
dtb_validate:
    /* Load magic number from offset 0 */
    ldr     w1, [x0]

    /* Check for DTB magic: 0xD00DFEED (big-endian) */
    /* In memory (little-endian view): 0xEDFE0DD0 */
    mov     w2, #0x0DD0
    movk    w2, #0xEDFE, lsl #16

    cmp     w1, w2
    b.eq    .Ldtb_valid

    /* Invalid magic */
    mov     x0, #-1
    ret

.Ldtb_valid:
    mov     x0, #0
    ret

.size dtb_validate, . - dtb_validate


.section .text
.global dtb_get_size
.type dtb_get_size, @function

/*
 * dtb_get_size(uint64_t dtb_addr)
 *   x0 = DTB address
 *   Returns: size in bytes (after byte-swap), or 0 if invalid
 *
 * The totalsize field is at offset 4 and is big-endian
 */
dtb_get_size:
    /* First validate the DTB */
    ldr     w1, [x0]
    mov     w2, #0x0DD0
    movk    w2, #0xEDFE, lsl #16
    cmp     w1, w2
    b.ne    .Ldtb_size_invalid

    /* Load totalsize from offset 4 (big-endian) */
    ldr     w0, [x0, #4]

    /* Byte-swap from big-endian to little-endian */
    rev     w0, w0
    ret

.Ldtb_size_invalid:
    mov     x0, #0
    ret

.size dtb_get_size, . - dtb_get_size
