/*
 * QEMU Virt Machine Bootloader - Unified Main
 * Uses common boot infrastructure with platform-specific hooks
 */

#include "bsp_config.h"
#include "../common/bsp.h"
#include "../common/boot_common.h"

/* ============================================================
 * Platform-Specific Hooks
 * ============================================================ */

void bsp_platform_init(void) {
    /* No additional initialization needed for virt */
}

void bsp_platform_tests(void) {
    /* No additional tests for virt */
}

void bsp_platform_banner(void) {
    /* Additional platform features */
    bsp_uart_puts("  [OK] PL011 UART\n");
    bsp_uart_puts("  [OK] ARM Generic Timer\n");
    bsp_uart_puts("  [OK] PL061 GPIO\n");
}

void bsp_platform_skipped(void) {
    bsp_uart_puts("  [SKIP] Virtio-blk - QEMU virt: no disk attached\n");
    bsp_uart_puts("  [SKIP] Virtio-net - QEMU virt: no network config\n");
    bsp_uart_puts("  [SKIP] GIC config - Basic boot, no IRQ handling\n");
    bsp_uart_puts("  [SKIP] SMP cores - Single core boot test\n");
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
