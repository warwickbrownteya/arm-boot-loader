/* ARM32 Linux Kernel Boot Header for Versatile Express
 *
 * ARM32 Boot Protocol (with DTB):
 *   r0 = 0 (unused, was previously machine type)
 *   r1 = 0xFFFFFFFF (indicates DTB-based boot)
 *   r2 = physical address of DTB
 *
 * For ATAG boot (legacy):
 *   r0 = 0
 *   r1 = machine type number
 *   r2 = physical address of ATAGS
 */

#ifndef KERNEL_BOOT_H
#define KERNEL_BOOT_H

#include <stdint.h>

/* Default load addresses for Versatile Express */
#define KERNEL_LOAD_ADDR    0x80008000    /* Standard ARM32 zImage load address */
#define DTB_LOAD_ADDR       0x88000000    /* DTB placed after kernel */

/* ARM32 zImage magic at offset 0x24 */
#define ARM32_ZIMAGE_MAGIC  0x016F2818

/* DTB magic (big-endian 0xD00DFEED, reads as little-endian 0xEDFE0DD0) */
#define DTB_MAGIC           0xEDFE0DD0

/* ARM32 zImage header structure */
typedef struct {
    uint32_t code[9];           /* ARM instructions, entry at offset 0 */
    uint32_t magic;             /* Magic at offset 0x24: 0x016F2818 */
    uint32_t start;             /* Start of zImage in RAM */
    uint32_t end;               /* End of zImage in RAM */
} __attribute__((packed)) arm32_zimage_header_t;

/* DTB header structure */
typedef struct {
    uint32_t magic;             /* 0xD00DFEED (big-endian) */
    uint32_t totalsize;         /* Total size in bytes */
    uint32_t off_dt_struct;     /* Offset to structure */
    uint32_t off_dt_strings;    /* Offset to strings */
    uint32_t off_mem_rsvmap;    /* Offset to memory reserve map */
    uint32_t version;           /* DTB version */
    uint32_t last_comp_version; /* Last compatible version */
    uint32_t boot_cpuid_phys;   /* Physical CPU ID */
    uint32_t size_dt_strings;   /* Size of strings block */
    uint32_t size_dt_struct;    /* Size of structure block */
} __attribute__((packed)) dtb_header_t;

/* Boot function - never returns */
void kernel_boot(uint32_t kernel_addr, uint32_t dtb_addr) __attribute__((noreturn));

/* Validation functions */
int kernel_validate(uint32_t kernel_addr);
int dtb_validate(uint32_t dtb_addr);
uint32_t dtb_get_size(uint32_t dtb_addr);

#endif /* KERNEL_BOOT_H */
