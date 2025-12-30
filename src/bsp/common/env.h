/*
 * ARM Bootloader - Environment Variable System
 * U-Boot compatible environment variables
 */

#ifndef ENV_H
#define ENV_H

#include "bsp.h"

/* ============================================================
 * Configuration
 * ============================================================ */

#define ENV_MAX_ENTRIES     32      /* Maximum number of variables */
#define ENV_NAME_SIZE       32      /* Maximum variable name length */
#define ENV_VALUE_SIZE      128     /* Maximum variable value length */

/* ============================================================
 * Environment Functions
 * ============================================================ */

/* Initialize the environment system */
void env_init(void);

/* Get a variable value (returns NULL if not set) */
const char *env_get(const char *name);

/* Set a variable (value=NULL deletes it) */
int env_set(const char *name, const char *value);

/* Delete a variable */
int env_delete(const char *name);

/* Print all variables */
void env_print_all(void);

/* Get number of defined variables */
int env_count(void);

/* ============================================================
 * Default Environment Variables
 * ============================================================ */

/*
 * Standard environment variables (U-Boot compatible):
 *
 * bootcmd     - Default boot command
 * bootargs    - Kernel command line
 * bootdelay   - Autoboot delay in seconds
 * baudrate    - UART baud rate
 * loadaddr    - Default load address for images
 * kernel_addr - Kernel load address
 * fdt_addr    - Device tree load address
 * initrd_addr - Initrd load address
 * ipaddr      - Board IP address
 * serverip    - TFTP server IP
 * gatewayip   - Gateway IP
 * netmask     - Network mask
 * ethaddr     - Ethernet MAC address
 * stdin       - Standard input device
 * stdout      - Standard output device
 * stderr      - Standard error device
 */

#endif /* ENV_H */
