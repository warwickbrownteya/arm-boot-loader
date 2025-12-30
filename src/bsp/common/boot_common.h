/*
 * ARM Bootloader - Common Boot Interface
 * Shared bootloader logic for all platforms
 */

#ifndef BOOT_COMMON_H
#define BOOT_COMMON_H

#include "bsp.h"
#include "kernel_boot.h"

/* ============================================================
 * Boot Configuration
 * Each BSP must define these in bsp_config.h or via Makefile
 * ============================================================ */

/* RAM_BASE should be defined by each BSP before including this header */
/* If not defined, provide a sensible default for compilation */
#ifndef RAM_BASE
    #warning "RAM_BASE not defined, using 0x0 default"
    #define RAM_BASE 0x0
#endif

/* Compute actual load addresses from RAM_BASE + offsets */
#ifndef KERNEL_LOAD_ADDR
    #define KERNEL_LOAD_ADDR    (RAM_BASE + KERNEL_LOAD_OFFSET)
#endif

#ifndef DTB_LOAD_ADDR
    #define DTB_LOAD_ADDR       (RAM_BASE + DTB_LOAD_OFFSET)
#endif

#ifndef INITRD_LOAD_ADDR
    #define INITRD_LOAD_ADDR    (RAM_BASE + INITRD_LOAD_OFFSET)
#endif

/* ============================================================
 * Common Boot Functions
 * ============================================================ */

/* Print a string to UART */
static inline void boot_puts(const char *s) {
    bsp_uart_puts(s);
}

/* Print hex value (64-bit for ARM64, 32-bit for ARM32) */
void boot_print_hex(kernel_addr_t val);

/* Print decimal value */
void boot_print_dec(uint32_t val);

/* Common boot banner */
void boot_print_banner(const bsp_info_t *info);

/* Print memory configuration */
void boot_print_memory_config(const bsp_info_t *info);

/* Run hardware tests and print results */
void boot_run_tests(const bsp_info_t *info);

/* Check for and boot kernel if present */
int boot_try_kernel(void);

/* Main boot loop (idle after all tests) */
void boot_idle_loop(void) __attribute__((noreturn));

/* Enter interactive shell */
void boot_shell(void) __attribute__((noreturn));

/* Autoboot with countdown (returns 0 if boot, -1 if interrupted) */
int boot_autoboot(int delay_sec);

/* ============================================================
 * Platform-Specific Hooks (BSP must implement)
 * ============================================================ */

/* Platform-specific initialization (called after BSP init) */
void bsp_platform_init(void);

/* Platform-specific tests (called during boot_run_tests) */
void bsp_platform_tests(void);

/* Platform-specific banner additions */
void bsp_platform_banner(void);

/* Platform-specific skipped checks list */
void bsp_platform_skipped(void);

#endif /* BOOT_COMMON_H */
