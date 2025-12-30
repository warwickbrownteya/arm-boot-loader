/*
 * ARM Bootloader - Raspberry Pi 3 Main Entry Point
 * BCM2837 SoC - GPU-First Boot Architecture
 *
 * Note: GPU has already initialized RAM and released ARM CPU
 * Entry point is 0x80000 (set by GPU firmware)
 */

#include "bsp_raspi.h"
#include "sd.h"
#include "kernel_boot.h"

/* Forward declarations for local functions */
static void print_hex64(uint64_t val);
static void print_hex32(uint32_t val);
static void print_line(void);

/* ========================================================================= */
/* Helper Functions                                                          */
/* ========================================================================= */

static void print_hex64(uint64_t val) {
    const char hex[] = "0123456789ABCDEF";
    char buf[19];
    buf[0] = '0';
    buf[1] = 'x';
    for (int i = 15; i >= 0; i--) {
        buf[17 - i] = hex[(val >> (i * 4)) & 0xF];
    }
    buf[18] = '\0';
    raspi_uart_puts(buf);
}

__attribute__((unused))
static void print_hex32(uint32_t val) {
    const char hex[] = "0123456789ABCDEF";
    char buf[11];
    buf[0] = '0';
    buf[1] = 'x';
    for (int i = 7; i >= 0; i--) {
        buf[9 - i] = hex[(val >> (i * 4)) & 0xF];
    }
    buf[10] = '\0';
    raspi_uart_puts(buf);
}

static void print_line(void) {
    raspi_uart_puts("========================================\n");
}

/* ========================================================================= */
/* Main Entry Point                                                          */
/* ========================================================================= */

void main(void) {
    uint64_t ticks1, ticks2;
    void *test_alloc;

    /* Initialize UART first for debug output */
    raspi_uart_init();

    /* Print banner */
    raspi_uart_puts("\n");
    print_line();
    raspi_uart_puts("  ARM Bootloader - Raspberry Pi 3\n");
    raspi_uart_puts("  BCM2837 - GPU-First Boot\n");
    print_line();

    /* Memory configuration */
    raspi_uart_puts("\nMemory Configuration:\n");
    raspi_uart_puts("  RAM Base: ");
    print_hex64(raspi_get_ram_base());
    raspi_uart_puts("\n");
    raspi_uart_puts("  RAM Size: ");
    print_hex64(raspi_get_ram_size());
    raspi_uart_puts(" (1 GB)\n");
    raspi_uart_puts("  UART Base: ");
    print_hex64(raspi_get_uart_base());
    raspi_uart_puts("\n");
    raspi_uart_puts("  GPIO Base: ");
    print_hex64(raspi_get_gpio_base());
    raspi_uart_puts("\n");

    /* UART test */
    raspi_uart_puts("\nUART Test:\n");
    raspi_uart_puts("  [OK] Mini UART initialized\n");
    raspi_uart_puts("  [OK] Serial output working\n");

    /* Timer test */
    raspi_uart_puts("\nTimer Test:\n");
    ticks1 = raspi_timer_get_ticks();
    raspi_uart_puts("  Initial ticks: ");
    print_hex64(ticks1);
    raspi_uart_puts("\n");

    raspi_timer_delay_ms(100);

    ticks2 = raspi_timer_get_ticks();
    raspi_uart_puts("  Ticks after 100ms: ");
    print_hex64(ticks2);
    raspi_uart_puts("\n");

    /* System timer runs at 1MHz, so 100ms = ~100000 ticks */
    if ((ticks2 - ticks1) > 50000) {
        raspi_uart_puts("  [OK] System Timer working\n");
    } else {
        raspi_uart_puts("  [WARN] Timer ticks seem low\n");
    }

    /* GPIO test */
    raspi_uart_puts("\nGPIO Test:\n");
    raspi_gpio_init();
    raspi_uart_puts("  [OK] GPIO initialized\n");

    /* LED blink test */
    raspi_uart_puts("  Blinking ACT LED...\n");
    raspi_led_blink(3, 200);
    raspi_uart_puts("  [OK] LED blink complete\n");

    /* Memory allocation test */
    raspi_uart_puts("\nMemory Test:\n");
    test_alloc = raspi_malloc(1024);
    if (test_alloc) {
        raspi_uart_puts("  Allocated 1KB at: ");
        print_hex64((uint64_t)(uintptr_t)test_alloc);
        raspi_uart_puts("\n");
        raspi_uart_puts("  [OK] Memory allocation working\n");
    } else {
        raspi_uart_puts("  [FAIL] Memory allocation failed\n");
    }

    /* SD Card test */
    raspi_uart_puts("\nSD Card Test:\n");
    if (sd_init() == 0) {
        raspi_uart_puts("  [OK] SD card initialized\n");

        /* Try to initialize FAT32 filesystem */
        if (fat_init() == 0) {
            raspi_uart_puts("  [OK] FAT32 filesystem mounted\n");

            /* Try to read a test file */
            uint32_t file_size = 0;
            raspi_uart_puts("  Looking for TEST.TXT...\n");
            if (fat_read_file("TEST.TXT", 0x100000, &file_size) == 0) {
                raspi_uart_puts("  [OK] Read TEST.TXT (");
                print_hex32(file_size);
                raspi_uart_puts(" bytes)\n");
                /* Print first 64 bytes */
                char *data = (char *)0x100000;
                raspi_uart_puts("  Content: ");
                for (uint32_t i = 0; i < file_size && i < 64; i++) {
                    if (data[i] >= 32 && data[i] < 127) {
                        raspi_uart_putc(data[i]);
                    }
                }
                raspi_uart_puts("\n");
            } else {
                raspi_uart_puts("  [INFO] TEST.TXT not found\n");
            }

            /* Try to load Device Tree Blob first */
            uint64_t dtb_addr = 0;
            uint32_t dtb_size = 0;

            raspi_uart_puts("  Looking for device tree...\n");

            /* Try platform-specific DTB first, then generic */
            if (fat_read_file("BCM2710-RPI-3-B.DTB", DTB_LOAD_ADDR, &dtb_size) == 0 ||
                fat_read_file("BCM2711-RPI-4-B.DTB", DTB_LOAD_ADDR, &dtb_size) == 0 ||
                fat_read_file("VIRT.DTB", DTB_LOAD_ADDR, &dtb_size) == 0 ||
                fat_read_file("DEVICE.DTB", DTB_LOAD_ADDR, &dtb_size) == 0) {

                /* Validate the DTB */
                if (dtb_validate(DTB_LOAD_ADDR) == 0) {
                    dtb_addr = DTB_LOAD_ADDR;
                    uint32_t actual_size = dtb_get_size(DTB_LOAD_ADDR);
                    raspi_uart_puts("  [OK] DTB loaded at ");
                    print_hex64(dtb_addr);
                    raspi_uart_puts(" (");
                    print_hex32(actual_size);
                    raspi_uart_puts(" bytes)\n");
                } else {
                    raspi_uart_puts("  [WARN] DTB file invalid\n");
                }
            } else {
                raspi_uart_puts("  [INFO] No DTB file found (kernel may have built-in)\n");
            }

            /* Try to read kernel8.img */
            raspi_uart_puts("  Looking for KERNEL8.IMG...\n");
            if (fat_read_file("KERNEL8.IMG", KERNEL_LOAD_ADDR, &file_size) == 0) {
                raspi_uart_puts("  [OK] Read KERNEL8.IMG (");
                print_hex32(file_size);
                raspi_uart_puts(" bytes)\n");

                /* Validate kernel header */
                if (kernel_validate(KERNEL_LOAD_ADDR) == 0) {
                    raspi_uart_puts("  [OK] Valid ARM64 kernel image\n");

                    /* Print kernel header info */
                    arm64_kernel_header_t *hdr = (arm64_kernel_header_t *)KERNEL_LOAD_ADDR;
                    raspi_uart_puts("  Image size: ");
                    print_hex64(hdr->image_size);
                    raspi_uart_puts("\n");
                    raspi_uart_puts("  Text offset: ");
                    print_hex64(hdr->text_offset);
                    raspi_uart_puts("\n");

                    raspi_uart_puts("\n");
                    print_line();
                    raspi_uart_puts("  BOOTING KERNEL\n");
                    print_line();
                    raspi_uart_puts("\nKernel: ");
                    print_hex64(KERNEL_LOAD_ADDR);
                    raspi_uart_puts("\n");
                    if (dtb_addr) {
                        raspi_uart_puts("DTB:    ");
                        print_hex64(dtb_addr);
                        raspi_uart_puts("\n");
                    } else {
                        raspi_uart_puts("DTB:    (none)\n");
                    }
                    raspi_uart_puts("\nJumping to kernel...\n\n");

                    /* Small delay for UART to flush */
                    raspi_timer_delay_ms(100);

                    /* Boot the kernel with DTB! */
                    kernel_boot(KERNEL_LOAD_ADDR, dtb_addr);
                    /* Never returns */
                } else {
                    raspi_uart_puts("  [WARN] Invalid kernel magic - not ARM64?\n");
                }
            } else {
                raspi_uart_puts("  [INFO] KERNEL8.IMG not found\n");
            }
        } else {
            raspi_uart_puts("  [INFO] FAT32 init failed (expected in QEMU without SD image)\n");
        }
    } else {
        raspi_uart_puts("  [INFO] SD init failed (expected in QEMU without SD emulation)\n");
    }

    /* If we get here, no kernel was booted - show status and idle */
    raspi_uart_puts("\nMailbox Test:\n");
    raspi_uart_puts("  [SKIP] Mailbox - QEMU raspi3b: limited emulation\n");

    raspi_uart_puts("\n");
    print_line();
    raspi_uart_puts("  BOOTLOADER READY\n");
    print_line();

    raspi_uart_puts("\nPlatform Features:\n");
    raspi_uart_puts("  [OK] Mini UART serial\n");
    raspi_uart_puts("  [OK] BCM System Timer (1MHz)\n");
    raspi_uart_puts("  [OK] GPIO controller\n");
    raspi_uart_puts("  [OK] Dynamic memory allocation\n");
    raspi_uart_puts("  [OK] SD/EMMC driver\n");
    raspi_uart_puts("  [OK] FAT32 filesystem\n");
    raspi_uart_puts("  [OK] DTB loader\n");
    raspi_uart_puts("  [OK] Kernel loader\n");

    raspi_uart_puts("\nConfiguration:\n");
    raspi_uart_puts("  Entry point: 0x80000 (GPU sets this)\n");
    raspi_uart_puts("  Kernel load: ");
    print_hex64(KERNEL_LOAD_ADDR);
    raspi_uart_puts("\n");
    raspi_uart_puts("  DTB load:    ");
    print_hex64(DTB_LOAD_ADDR);
    raspi_uart_puts("\n");
    raspi_uart_puts("  Peripheral base: 0x3F000000 (Pi3)\n");

    raspi_uart_puts("\nNo kernel found. Waiting...\n");

    /* Enter idle loop */
    while (1) {
        __asm__ volatile("wfe");
    }
}
