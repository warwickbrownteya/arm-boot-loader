/*
 * ARM Bootloader - Boot Script Support
 * U-Boot compatible script execution
 */

#ifndef SCRIPT_H
#define SCRIPT_H

#include "bsp.h"

/* ============================================================
 * Script Format
 * ============================================================
 *
 * Scripts are plain text with one command per line.
 * Lines starting with '#' are comments.
 * Empty lines are ignored.
 *
 * Example script:
 *   # Boot script
 *   setenv bootargs console=ttyAMA0
 *   boot
 *
 * U-Boot mkimage format is also supported (for compatibility).
 */

/* ============================================================
 * Script Functions
 * ============================================================ */

/* Execute a script from memory
 * addr: Address of script in memory
 * len:  Length of script (0 = null-terminated)
 * Returns: 0 on success, -1 on error
 */
int script_run(bsp_addr_t addr, uint32_t len);

/* Execute a script from environment variable
 * name: Environment variable containing script commands
 * Returns: 0 on success, -1 on error
 */
int script_run_env(const char *name);

/* Execute bootcmd (default boot command)
 * Returns: 0 on success, -1 on error
 */
int script_run_bootcmd(void);

/* ============================================================
 * U-Boot mkimage Header
 * ============================================================ */

#define IH_MAGIC    0x27051956  /* Image Magic Number */
#define IH_NMLEN    32          /* Image Name Length */

/* Image types */
#define IH_TYPE_SCRIPT      6   /* Script file */
#define IH_TYPE_KERNEL      2   /* Kernel image */

typedef struct {
    uint32_t    ih_magic;       /* Image Magic Number */
    uint32_t    ih_hcrc;        /* Header CRC */
    uint32_t    ih_time;        /* Creation Time Stamp */
    uint32_t    ih_size;        /* Image Data Size */
    uint32_t    ih_load;        /* Load Address */
    uint32_t    ih_ep;          /* Entry Point */
    uint32_t    ih_dcrc;        /* Data CRC */
    uint8_t     ih_os;          /* Operating System */
    uint8_t     ih_arch;        /* CPU architecture */
    uint8_t     ih_type;        /* Image Type */
    uint8_t     ih_comp;        /* Compression Type */
    uint8_t     ih_name[IH_NMLEN];  /* Image Name */
} uboot_image_header_t;

/* Check if address points to U-Boot image */
int script_is_uboot_image(bsp_addr_t addr);

/* Get script from U-Boot image */
const char *script_get_uboot_data(bsp_addr_t addr, uint32_t *len);

#endif /* SCRIPT_H */
