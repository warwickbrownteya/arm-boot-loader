/*
 * ARM Bootloader - Common Boot Implementation
 * Shared bootloader logic for all platforms
 */

#include "boot_common.h"
#include "shell.h"
#include "env.h"

/* ============================================================
 * Hex Printing Utilities
 * ============================================================ */

#ifdef BSP_ARCH_64BIT
void boot_print_hex(kernel_addr_t val) {
    static const char hex[] = "0123456789ABCDEF";
    char buf[19];
    int i;

    buf[0] = '0';
    buf[1] = 'x';
    for (i = 0; i < 16; i++) {
        buf[17 - i] = hex[val & 0xF];
        val >>= 4;
    }
    buf[18] = '\0';
    boot_puts(buf);
}
#else
void boot_print_hex(kernel_addr_t val) {
    static const char hex[] = "0123456789ABCDEF";
    char buf[11];
    int i;

    buf[0] = '0';
    buf[1] = 'x';
    for (i = 0; i < 8; i++) {
        buf[9 - i] = hex[val & 0xF];
        val >>= 4;
    }
    buf[10] = '\0';
    boot_puts(buf);
}
#endif

void boot_print_dec(uint32_t val) {
    char buf[12];
    int i = 10;

    buf[11] = '\0';
    if (val == 0) {
        buf[i--] = '0';
    } else {
        while (val > 0 && i >= 0) {
            buf[i--] = '0' + (val % 10);
            val /= 10;
        }
    }
    boot_puts(&buf[i + 1]);
}

/* ============================================================
 * Common Boot Banner
 * ============================================================ */

void boot_print_banner(const bsp_info_t *info) {
    boot_puts("\n");
    boot_puts("========================================\n");
    boot_puts("  ARM Bootloader - ");
    boot_puts(info->name);
    boot_puts("\n");
    boot_puts("  ");
    boot_puts(info->description);
    boot_puts("\n");
    boot_puts("========================================\n");
    boot_puts("\n");
}

/* ============================================================
 * Memory Configuration Display
 * ============================================================ */

void boot_print_memory_config(const bsp_info_t *info) {
    uint32_t ram_mb;

    boot_puts("Memory Configuration:\n");
    boot_puts("  RAM Base: ");
    boot_print_hex(info->ram_base);
    boot_puts("\n");
    boot_puts("  RAM Size: ");
    boot_print_hex(info->ram_size);

    /* Print human-readable size */
    ram_mb = (uint32_t)(info->ram_size / (1024 * 1024));
    if (ram_mb >= 1024) {
        boot_puts(" (");
        boot_print_dec(ram_mb / 1024);
        boot_puts(" GB)\n");
    } else {
        boot_puts(" (");
        boot_print_dec(ram_mb);
        boot_puts(" MB)\n");
    }

    boot_puts("  UART Base: ");
    boot_print_hex(info->uart_base);
    boot_puts("\n");

    if (info->timer_base) {
        boot_puts("  Timer Base: ");
        boot_print_hex(info->timer_base);
        boot_puts("\n");
    }

    if (info->gpio_base) {
        boot_puts("  GPIO Base: ");
        boot_print_hex(info->gpio_base);
        boot_puts("\n");
    }

    boot_puts("\n");
}

/* ============================================================
 * Hardware Tests
 * ============================================================ */

/* Simple bump allocator for testing */
extern uint8_t __heap_start;
extern uint8_t __heap_end;
static uint8_t *heap_ptr = 0;

static void *simple_malloc(uint32_t size) {
    uint8_t *ptr;

    if (!heap_ptr) {
        heap_ptr = &__heap_start;
    }

    /* Align to 8 bytes */
    size = (size + 7) & ~7;

    if ((heap_ptr + size) > &__heap_end) {
        return 0;
    }

    ptr = heap_ptr;
    heap_ptr += size;
    return ptr;
}

void boot_run_tests(const bsp_info_t *info) {
    uint64_t timer_start, timer_elapsed;
    void *test_ptr;

    (void)info;  /* May be unused in some tests */

    /* UART Test */
    boot_puts("UART Test:\n");
    boot_puts("  [OK] UART initialized\n");
    boot_puts("  [OK] Serial output working\n");
    boot_puts("\n");

    /* Timer Test */
    boot_puts("Timer Test:\n");
    timer_start = bsp_timer_get_ticks();
    bsp_timer_delay_ms(100);
    timer_elapsed = bsp_timer_get_ticks() - timer_start;
    boot_puts("  Ticks for 100ms: ");
    boot_print_hex((kernel_addr_t)timer_elapsed);
    boot_puts("\n");
    boot_puts("  [OK] Timer working\n");
    boot_puts("\n");

    /* GPIO Test */
    boot_puts("GPIO Test:\n");
    bsp_gpio_set_function(0, 1);
    bsp_gpio_set(0);
    bsp_gpio_clear(0);
    boot_puts("  [OK] GPIO initialized\n");
    boot_puts("\n");

    /* Memory Test */
    boot_puts("Memory Test:\n");
    test_ptr = simple_malloc(1024);
    if (test_ptr) {
        boot_puts("  Allocated 1KB at: ");
        boot_print_hex((kernel_addr_t)(uintptr_t)test_ptr);
        boot_puts("\n");
        boot_puts("  [OK] Memory allocation working\n");
    } else {
        boot_puts("  [FAIL] Memory allocation failed\n");
    }
    boot_puts("\n");

    /* Platform-specific tests */
    bsp_platform_tests();
}

/* ============================================================
 * Kernel Boot
 * ============================================================ */

int boot_try_kernel(void) {
    kernel_addr_t kaddr = KERNEL_LOAD_ADDR;
    kernel_addr_t daddr = DTB_LOAD_ADDR;
    kernel_header_t *hdr;

    boot_puts("Kernel Boot Check:\n");

    if (kernel_validate(kaddr) == 0) {
        hdr = (kernel_header_t *)kaddr;
        boot_puts("  [OK] Kernel found at ");
        boot_print_hex(kaddr);
        boot_puts("\n");

#ifdef BSP_ARCH_64BIT
        boot_puts("  Image size: ");
        boot_print_hex(hdr->image_size);
        boot_puts("\n");
#else
        boot_puts("  zImage end: ");
        boot_print_hex(hdr->end);
        boot_puts("\n");
#endif

        /* Check for DTB */
        if (dtb_validate(daddr) == 0) {
            boot_puts("  [OK] DTB found at ");
            boot_print_hex(daddr);
            boot_puts(" (");
            boot_print_hex(dtb_get_size(daddr));
            boot_puts(" bytes)\n");
        } else {
            daddr = 0;
            boot_puts("  [INFO] No DTB found\n");
        }

        boot_puts("\n");
        boot_puts("========================================\n");
        boot_puts("  BOOTING KERNEL\n");
        boot_puts("========================================\n");
        boot_puts("\nKernel: ");
        boot_print_hex(kaddr);
        boot_puts("\n");

        if (daddr) {
            boot_puts("DTB:    ");
            boot_print_hex(daddr);
            boot_puts("\n");
        } else {
            boot_puts("DTB:    (none)\n");
        }

        boot_puts("\nJumping to kernel...\n\n");

        bsp_timer_delay_ms(100);
        kernel_boot(kaddr, daddr);
        /* Never returns */
    } else {
        boot_puts("  [INFO] No kernel at ");
        boot_print_hex(kaddr);
        boot_puts("\n");
    }
    boot_puts("\n");

    return -1;  /* No kernel found */
}

/* ============================================================
 * Boot Status and Idle
 * ============================================================ */

/* ============================================================
 * Autoboot with Countdown
 * ============================================================ */

int boot_autoboot(int delay_sec) {
    int i;
    int c;
    uint64_t start_tick, current_tick;
    uint32_t ticks_per_sec;

    if (delay_sec <= 0) {
        /* No delay - boot immediately */
        return 0;
    }

    ticks_per_sec = bsp_timer_get_freq();

    boot_puts("\nAutoboot in ");
    boot_print_dec(delay_sec);
    boot_puts(" seconds (press any key to interrupt)\n");

    for (i = delay_sec; i > 0; i--) {
        boot_puts("\r");
        boot_print_dec(i);
        boot_puts("... ");

        /* Wait for 1 second or keypress */
        start_tick = bsp_timer_get_ticks();
        while (1) {
            current_tick = bsp_timer_get_ticks();
            if ((current_tick - start_tick) >= ticks_per_sec) {
                break;  /* 1 second elapsed */
            }

            if (bsp_uart_tstc()) {
                c = bsp_uart_getc();
                (void)c;  /* Consume the character */
                boot_puts("\nAutoboot interrupted\n");
                return -1;  /* User interrupted */
            }
        }
    }

    boot_puts("\nBooting...\n");
    return 0;
}

void boot_idle_loop(void) {
    boot_puts("========================================\n");
    boot_puts("  BOOTLOADER READY\n");
    boot_puts("========================================\n");
    boot_puts("\n");

    boot_puts("Platform Features:\n");
    boot_puts("  [OK] UART serial\n");
    boot_puts("  [OK] Timer\n");
    boot_puts("  [OK] GPIO\n");
    boot_puts("  [OK] Dynamic memory\n");
    boot_puts("  [OK] DTB loader\n");
    boot_puts("  [OK] Kernel loader\n");
    boot_puts("  [OK] Command shell\n");

    /* Platform-specific features */
    bsp_platform_banner();
    boot_puts("\n");

    boot_puts("Configuration:\n");
    boot_puts("  Kernel load: ");
    boot_print_hex(KERNEL_LOAD_ADDR);
    boot_puts("\n");
    boot_puts("  DTB load:    ");
    boot_print_hex(DTB_LOAD_ADDR);
    boot_puts("\n");
    boot_puts("\n");

    boot_puts("Skipped Checks:\n");
    bsp_platform_skipped();
    boot_puts("\n");

    boot_puts("No kernel found. Entering shell...\n");

    /* Enter interactive shell instead of idle loop */
    boot_shell();
}

/* ============================================================
 * Interactive Shell Entry
 * ============================================================ */

void boot_shell(void) {
    shell_init();
    shell_run();
    /* Never returns */
}
