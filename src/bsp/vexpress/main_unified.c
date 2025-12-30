/*
 * ARM Versatile Express A15 Bootloader - Unified Main
 * Uses common boot infrastructure with platform-specific hooks
 * ARMv7-A 32-bit platform
 */

#include "bsp_config.h"
#include "../common/bsp.h"
#include "../common/boot_common.h"

/* Forward declarations for vexpress-specific functions */
extern uint32_t vexpress_get_board_id(void);
extern uint32_t vexpress_get_proc_id(void);

/* ============================================================
 * Platform-Specific Hooks
 * ============================================================ */

void bsp_platform_init(void) {
    /* No additional initialization needed */
}

void bsp_platform_tests(void) {
    /* Board identification */
    boot_puts("Board Information:\n");
    boot_puts("  Board ID: ");
    boot_print_hex(vexpress_get_board_id());
    boot_puts("\n");
    boot_puts("  Proc ID:  ");
    boot_print_hex(vexpress_get_proc_id());
    boot_puts("\n");
    boot_puts("\n");

    /* LED test */
    boot_puts("LED Test:\n");
    boot_puts("  Blinking system LEDs...\n");
    for (int i = 0; i < 8; i++) {
        bsp_gpio_set(i);
        bsp_timer_delay_ms(50);
        bsp_gpio_clear(i);
    }
    boot_puts("  [OK] LED test complete\n");
    boot_puts("\n");
}

void bsp_platform_banner(void) {
    /* Additional platform features */
    boot_puts("  [OK] PL011 UART\n");
    boot_puts("  [OK] SP804 Timer (1MHz)\n");
    boot_puts("  [OK] System LEDs\n");
}

void bsp_platform_skipped(void) {
    boot_puts("  [SKIP] VirtIO devices - QEMU vexpress: not attached\n");
    boot_puts("  [SKIP] GIC config - Basic boot, no IRQ handling\n");
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
