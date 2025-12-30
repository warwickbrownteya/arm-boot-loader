/*
 * ARM Bootloader - Kernel Boot Header
 * ARM64 Linux Boot Protocol Implementation
 */

#ifndef KERNEL_BOOT_H
#define KERNEL_BOOT_H

#include <stdint.h>

/* RAM base for QEMU virt machine (SBSA uses virt) */
#define RAM_BASE            0x40000000

/* Kernel load address - RAM base + standard offset */
#define KERNEL_LOAD_ADDR    (RAM_BASE + 0x80000)

/* Device tree blob address */
#define DTB_LOAD_ADDR       (RAM_BASE + 0x100000)

/* Initrd load address */
#define INITRD_LOAD_ADDR    0x8000000

/*
 * Boot the loaded kernel
 * kernel_addr: physical address where kernel is loaded
 * dtb_addr: physical address of DTB (0 if none)
 *
 * ARM64 boot protocol:
 *   x0 = physical address of device tree blob
 *   x1 = 0 (reserved)
 *   x2 = 0 (reserved)
 *   x3 = 0 (reserved)
 *
 * This function does not return.
 */
void kernel_boot(uint64_t kernel_addr, uint64_t dtb_addr) __attribute__((noreturn));

/*
 * Validate ARM64 kernel image header
 * Returns: 0 if valid, -1 if invalid
 */
int kernel_validate(uint64_t kernel_addr);

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
} arm64_kernel_header_t;

/* ARM64 kernel magic number */
#define ARM64_KERNEL_MAGIC  0x644d5241  /* "ARM\x64" little-endian */

/* ============================================================
 * Device Tree Blob (DTB) Support
 * ============================================================ */

/* DTB magic number: 0xD00DFEED in big-endian */
#define DTB_MAGIC           0xEDFE0DD0  /* As seen in little-endian memory */
#define DTB_MAGIC_BE        0xD00DFEED  /* Big-endian value */

/* Common DTB filenames to search for */
#define DTB_FILENAME_PI3    "BCM2710-RPI-3-B.DTB"
#define DTB_FILENAME_PI4    "BCM2711-RPI-4-B.DTB"
#define DTB_FILENAME_GENERIC "DTB"

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

/*
 * Validate Device Tree Blob
 * Returns: 0 if valid, -1 if invalid
 */
int dtb_validate(uint64_t dtb_addr);

/*
 * Get DTB total size (converts from big-endian)
 * Returns: size in bytes, or 0 if invalid
 */
uint32_t dtb_get_size(uint64_t dtb_addr);

/*
 * Byte swap for big-endian to little-endian conversion
 */
static inline uint32_t bswap32(uint32_t val) {
    return ((val & 0xFF000000) >> 24) |
           ((val & 0x00FF0000) >> 8)  |
           ((val & 0x0000FF00) << 8)  |
           ((val & 0x000000FF) << 24);
}

#endif /* KERNEL_BOOT_H */
