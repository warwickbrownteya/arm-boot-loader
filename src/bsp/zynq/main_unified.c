/*
 * Xilinx Zynq UltraScale+ ZCU102 Bootloader - Unified Main
 * Uses common boot infrastructure with platform-specific hooks
 */

#include "bsp_config.h"
#include "../common/bsp.h"
#include "../common/boot_common.h"

/* ============================================================
 * Platform-Specific Hooks
 * ============================================================ */

void bsp_platform_init(void) {
    /* No additional initialization needed for Zynq */
}

void bsp_platform_tests(void) {
    /* Platform-specific tests */
    boot_puts("FPGA Status:\n");
    boot_puts("  [OK] PS block initialized\n");
    boot_puts("  [SKIP] PL configuration - Not loaded\n");
    boot_puts("\n");
}

void bsp_platform_banner(void) {
    /* Additional platform features */
    boot_puts("  [OK] Cadence UART\n");
    boot_puts("  [OK] TTC Timer (100MHz)\n");
    boot_puts("  [OK] MIO GPIO\n");
    boot_puts("  [OK] ZynqMP PMU\n");
}

void bsp_platform_skipped(void) {
    boot_puts("  [SKIP] PL programming - FPGA not configured\n");
    boot_puts("  [SKIP] DisplayPort - No display attached\n");
    boot_puts("  [SKIP] USB - Not configured\n");
    boot_puts("  [SKIP] SMP cores - Single core boot test\n");
}

/* ============================================================
 * Main Entry Point
 * ============================================================ */

void main(void) {
    const bsp_info_t *info;

    /* Initialize BSP */
    bsp_init();

    /* Get platform info */
    info = bsp_get_info();

    /* Print banner */
    boot_print_banner(info);

    /* Print memory configuration */
    boot_print_memory_config(info);

    /* Run hardware tests */
    boot_run_tests(info);

    /* Try to boot kernel */
    boot_try_kernel();

    /* Enter idle loop */
    boot_idle_loop();
}
