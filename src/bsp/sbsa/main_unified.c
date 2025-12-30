/*
 * ARM SBSA-Compatible Platform Bootloader - Unified Main
 * Uses common boot infrastructure with platform-specific hooks
 */

#include "bsp_config.h"
#include "../common/bsp.h"
#include "../common/boot_common.h"
#include "bsp_sbsa.h"

/* Forward declaration of accessor functions */
extern uint64_t sbsa_get_pcie_ecam_base(void);

/* ============================================================
 * Platform-Specific Hooks
 * ============================================================ */

void bsp_platform_init(void) {
    /* No additional initialization needed for SBSA */
}

void bsp_platform_tests(void) {
    /* System Information */
    boot_puts("System Information:\n");
    boot_puts("  Platform: SBSA Compatible\n");
    boot_puts("  GIC: v3\n");
    boot_puts("\n");

    /* PCIe Configuration */
    boot_puts("PCIe Configuration:\n");
    boot_puts("  ECAM Base: ");
    boot_print_hex(sbsa_get_pcie_ecam_base());
    boot_puts("\n");
    boot_puts("\n");
}

void bsp_platform_banner(void) {
    /* Additional platform features */
    boot_puts("  [OK] PL011 UART\n");
    boot_puts("  [OK] ARM Generic Timer\n");
    boot_puts("  [OK] PL061 GPIO\n");
    boot_puts("  [OK] GICv3 Interrupt Controller\n");
    boot_puts("  [OK] PCIe support\n");
}

void bsp_platform_skipped(void) {
    boot_puts("  [SKIP] PCIe enumeration - QEMU virt: no devices\n");
    boot_puts("  [SKIP] GIC config - Basic boot, no IRQ handling\n");
    boot_puts("  [SKIP] SMP cores - Single core boot test\n");
    boot_puts("  [SKIP] SMMU - Not configured\n");
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
