/*
 * Raspberry Pi 3 Bootloader - Unified Main
 * Uses common boot infrastructure with platform-specific hooks
 * Includes SD card and FAT32 filesystem support
 */

#include "bsp_config.h"
#include "../common/bsp.h"
#include "../common/boot_common.h"
#include "sd.h"

/* Forward declarations */
static void try_load_kernel_from_sd(void);

/* ============================================================
 * Platform-Specific Hooks
 * ============================================================ */

void bsp_platform_init(void) {
    /* SD card and FAT32 filesystem initialization will be done in tests */
}

void bsp_platform_tests(void) {
    /* SD Card test - this also attempts to load kernel */
    boot_puts("SD Card Test:\n");

    if (sd_init() == 0) {
        boot_puts("  [OK] SD card initialized\n");

        /* Try to initialize FAT32 filesystem */
        if (fat_init() == 0) {
            boot_puts("  [OK] FAT32 filesystem mounted\n");

            /* Try to read a test file */
            uint32_t file_size = 0;
            boot_puts("  Looking for TEST.TXT...\n");
            if (fat_read_file("TEST.TXT", 0x100000, &file_size) == 0) {
                boot_puts("  [OK] Read TEST.TXT (");
                boot_print_hex(file_size);
                boot_puts(" bytes)\n");
            } else {
                boot_puts("  [INFO] TEST.TXT not found\n");
            }

            /* Attempt to load kernel and DTB from SD card */
            try_load_kernel_from_sd();

        } else {
            boot_puts("  [INFO] FAT32 init failed (expected in QEMU without SD image)\n");
        }
    } else {
        boot_puts("  [INFO] SD init failed (expected in QEMU without SD emulation)\n");
    }
    boot_puts("\n");

    /* LED blink test */
    boot_puts("LED Test:\n");
    boot_puts("  Blinking ACT LED...\n");
    /* Note: Uses GPIO functions through bsp interface */
    bsp_gpio_set_function(29, 1);  /* ACT LED is GPIO 29 on Pi3 */
    for (int i = 0; i < 3; i++) {
        bsp_gpio_clear(29);  /* LED on (active low) */
        bsp_timer_delay_ms(200);
        bsp_gpio_set(29);    /* LED off */
        bsp_timer_delay_ms(200);
    }
    boot_puts("  [OK] LED blink complete\n");
    boot_puts("\n");
}

void bsp_platform_banner(void) {
    /* Additional platform features */
    boot_puts("  [OK] Mini UART serial\n");
    boot_puts("  [OK] BCM System Timer (1MHz)\n");
    boot_puts("  [OK] SD/EMMC driver\n");
    boot_puts("  [OK] FAT32 filesystem\n");
}

void bsp_platform_skipped(void) {
    boot_puts("  [SKIP] Mailbox - QEMU raspi3b: limited emulation\n");
    boot_puts("  [SKIP] SMP cores - Single core boot test\n");
}

/* ============================================================
 * SD Card Kernel Loading
 * ============================================================ */

static void try_load_kernel_from_sd(void) {
    uint32_t file_size = 0;

    /* Try to load Device Tree Blob first */
    boot_puts("  Looking for device tree...\n");

    if (fat_read_file("BCM2710-RPI-3-B.DTB", DTB_LOAD_ADDR, &file_size) == 0 ||
        fat_read_file("BCM2711-RPI-4-B.DTB", DTB_LOAD_ADDR, &file_size) == 0 ||
        fat_read_file("VIRT.DTB", DTB_LOAD_ADDR, &file_size) == 0 ||
        fat_read_file("DEVICE.DTB", DTB_LOAD_ADDR, &file_size) == 0) {

        if (dtb_validate(DTB_LOAD_ADDR) == 0) {
            boot_puts("  [OK] DTB loaded at ");
            boot_print_hex(DTB_LOAD_ADDR);
            boot_puts(" (");
            boot_print_hex(dtb_get_size(DTB_LOAD_ADDR));
            boot_puts(" bytes)\n");
        } else {
            boot_puts("  [WARN] DTB file invalid\n");
        }
    } else {
        boot_puts("  [INFO] No DTB file found (kernel may have built-in)\n");
    }

    /* Try to read kernel8.img */
    boot_puts("  Looking for KERNEL8.IMG...\n");
    if (fat_read_file("KERNEL8.IMG", KERNEL_LOAD_ADDR, &file_size) == 0) {
        boot_puts("  [OK] Read KERNEL8.IMG (");
        boot_print_hex(file_size);
        boot_puts(" bytes)\n");

        /* Validate kernel header */
        if (kernel_validate(KERNEL_LOAD_ADDR) == 0) {
            boot_puts("  [OK] Valid ARM64 kernel image loaded to ");
            boot_print_hex(KERNEL_LOAD_ADDR);
            boot_puts("\n");
            /* boot_try_kernel() will find and boot this kernel */
        } else {
            boot_puts("  [WARN] Invalid kernel magic - not ARM64?\n");
        }
    } else {
        boot_puts("  [INFO] KERNEL8.IMG not found\n");
    }
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

    /* Run hardware tests (includes SD card and kernel loading) */
    boot_run_tests(info);

    /* Try to boot kernel (if loaded from SD or already in memory) */
    boot_try_kernel();

    /* Enter idle loop */
    boot_idle_loop();
}
