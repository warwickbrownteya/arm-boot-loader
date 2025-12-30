/*
 * ARM Bootloader - Unified Kernel Boot Header
 * Supports ARM64 (AArch64) and ARM32 (ARMv7-A) platforms
 *
 * This is the common kernel boot interface. Each BSP provides
 * platform-specific load addresses via bsp_kernel_config.h
 */

#ifndef KERNEL_BOOT_H
#define KERNEL_BOOT_H

#include <stdint.h>
#include "bsp.h"

/* ============================================================
 * Architecture Detection
 * ============================================================ */

#ifdef BSP_ARCH_64BIT
    #define KERNEL_ARCH_ARM64   1
    typedef uint64_t kernel_addr_t;
#else
    #define KERNEL_ARCH_ARM32   1
    typedef uint32_t kernel_addr_t;
#endif

/* ============================================================
 * Default Load Addresses (can be overridden per-BSP)
 * ============================================================ */

#ifndef KERNEL_LOAD_OFFSET
    #ifdef KERNEL_ARCH_ARM64
        #define KERNEL_LOAD_OFFSET  0x80000     /* ARM64 standard */
    #else
        #define KERNEL_LOAD_OFFSET  0x8000      /* ARM32 zImage standard */
    #endif
#endif

#ifndef DTB_LOAD_OFFSET
    #define DTB_LOAD_OFFSET     0x100000        /* 1MB offset for DTB */
#endif

#ifndef INITRD_LOAD_OFFSET
    #define INITRD_LOAD_OFFSET  0x8000000       /* 128MB offset for initrd */
#endif

/* ============================================================
 * Kernel Image Structures
 * ============================================================ */

#ifdef KERNEL_ARCH_ARM64
/*
 * ARM64 kernel image header (first 64 bytes)
 * See: Documentation/arch/arm64/booting.rst
 */
typedef struct {
    uint32_t code0;         /* Executable code or branch */
    uint32_t code1;         /* Executable code */
    uint64_t text_offset;   /* Image load offset */
    uint64_t image_size;    /* Effective image size */
    uint64_t flags;         /* Kernel flags */
    uint64_t res2;          /* Reserved */
    uint64_t res3;          /* Reserved */
    uint64_t res4;          /* Reserved */
    uint32_t magic;         /* Magic: 0x644d5241 "ARM\x64" */
    uint32_t res5;          /* Reserved (PE header offset) */
} __attribute__((packed)) kernel_header_t;

/* ARM64 kernel magic number */
#define KERNEL_MAGIC    0x644d5241  /* "ARM\x64" little-endian */

#else /* KERNEL_ARCH_ARM32 */
/*
 * ARM32 zImage header
 * Magic at offset 0x24
 */
typedef struct {
    uint32_t code[9];       /* ARM instructions, entry at offset 0 */
    uint32_t magic;         /* Magic at offset 0x24: 0x016F2818 */
    uint32_t start;         /* Start of zImage in RAM */
    uint32_t end;           /* End of zImage in RAM */
} __attribute__((packed)) kernel_header_t;

/* ARM32 zImage magic number */
#define KERNEL_MAGIC    0x016F2818

#endif

/* ============================================================
 * Device Tree Blob (DTB) Support
 * ============================================================ */

/* DTB magic number: 0xD00DFEED in big-endian */
#define DTB_MAGIC       0xEDFE0DD0  /* As seen in little-endian memory */
#define DTB_MAGIC_BE    0xD00DFEED  /* Big-endian value */

/*
 * Device Tree Blob header structure
 * All fields are big-endian!
 */
typedef struct {
    uint32_t magic;             /* 0x00: Magic number (0xD00DFEED) */
    uint32_t totalsize;         /* 0x04: Total size of DTB */
    uint32_t off_dt_struct;     /* 0x08: Offset to structure block */
    uint32_t off_dt_strings;    /* 0x0C: Offset to strings block */
    uint32_t off_mem_rsvmap;    /* 0x10: Offset to memory reservation block */
    uint32_t version;           /* 0x14: DTB version */
    uint32_t last_comp_version; /* 0x18: Last compatible version */
    uint32_t boot_cpuid_phys;   /* 0x1C: Physical CPU ID for boot */
    uint32_t size_dt_strings;   /* 0x20: Size of strings block */
    uint32_t size_dt_struct;    /* 0x24: Size of structure block */
} __attribute__((packed)) dtb_header_t;

/* ============================================================
 * Kernel Boot Functions
 * ============================================================ */

/*
 * Boot the loaded kernel
 *
 * ARM64 boot protocol:
 *   x0 = physical address of device tree blob
 *   x1 = 0 (reserved)
 *   x2 = 0 (reserved)
 *   x3 = 0 (reserved)
 *
 * ARM32 boot protocol (with DTB):
 *   r0 = 0
 *   r1 = 0xFFFFFFFF (indicates DTB boot)
 *   r2 = physical address of DTB
 *
 * This function does not return.
 */
void kernel_boot(kernel_addr_t kernel_addr, kernel_addr_t dtb_addr) __attribute__((noreturn));

/*
 * Validate kernel image header
 * Returns: 0 if valid, -1 if invalid
 */
int kernel_validate(kernel_addr_t kernel_addr);

/*
 * Validate Device Tree Blob
 * Returns: 0 if valid, -1 if invalid
 */
int dtb_validate(kernel_addr_t dtb_addr);

/*
 * Get DTB total size (converts from big-endian)
 * Returns: size in bytes, or 0 if invalid
 */
uint32_t dtb_get_size(kernel_addr_t dtb_addr);

/* ============================================================
 * Utility Functions
 * ============================================================ */

/* Byte swap for big-endian to little-endian conversion */
static inline uint32_t bswap32(uint32_t val) {
    return ((val & 0xFF000000) >> 24) |
           ((val & 0x00FF0000) >> 8)  |
           ((val & 0x0000FF00) << 8)  |
           ((val & 0x000000FF) << 24);
}

#endif /* KERNEL_BOOT_H */
