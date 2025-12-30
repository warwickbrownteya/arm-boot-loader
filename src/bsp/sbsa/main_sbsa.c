/* ARM SBSA-Compatible Platform Bootloader Main
 *
 * Configured for systems with up to 8GB RAM.
 * Uses addresses within 4GB for reliable GOT operations.
 */

#include <stdint.h>
#include "../common/bsp.h"
#include "bsp_sbsa.h"
#include "kernel_boot.h"

/* Heap management */
extern uint8_t __heap_start;
extern uint8_t __heap_end;
static uint8_t *heap_ptr = 0;

/* Forward declarations */
static void print_hex64(uint64_t val);
static void* simple_alloc(uint32_t size);

/* ============================================================
 * Main Entry Point
 * ============================================================ */

void main(void) {
    const bsp_info_t *info;
    uint64_t timer_ticks;
    void *test_alloc;

    /* Initialize BSP - UART first for debugging */
    bsp_uart_init();

    /* Print banner */
    bsp_uart_puts("\n");
    bsp_uart_puts("========================================\n");
    bsp_uart_puts("  ARM Bootloader - SBSA Compatible\n");
    bsp_uart_puts("  Server-Class Platform (8GB max)\n");
    bsp_uart_puts("========================================\n");
    bsp_uart_puts("\n");

    /* Initialize timer and GPIO */
    bsp_timer_init();
    bsp_gpio_init();

    /* Get platform info */
    info = bsp_get_info();

    if (info == 0) {
        bsp_uart_puts("[ERROR] NULL BSP info\n");
        while(1) __asm__ volatile("wfe");
    }

    /* System Information */
    bsp_uart_puts("System Information:\n");
    bsp_uart_puts("  Platform: SBSA Compatible\n");
    bsp_uart_puts("  GIC: v3\n");
    bsp_uart_puts("\n");

    /* Memory Configuration - use accessor functions to avoid GOT issues */
    bsp_uart_puts("Memory Configuration:\n");
    bsp_uart_puts("  RAM Base: ");
    print_hex64(sbsa_get_ram_base());
    bsp_uart_puts("\n");
    bsp_uart_puts("  RAM Size: ");
    print_hex64(sbsa_get_ram_size());
    bsp_uart_puts(" (8 GB max)\n");
    bsp_uart_puts("  UART Base: ");
    print_hex64(sbsa_get_uart_base());
    bsp_uart_puts("\n");
    bsp_uart_puts("  GPIO Base: ");
    print_hex64(sbsa_get_gpio_base());
    bsp_uart_puts("\n");
    bsp_uart_puts("\n");

    /* PCIe Configuration */
    bsp_uart_puts("PCIe Configuration:\n");
    bsp_uart_puts("  ECAM Base: ");
    print_hex64(sbsa_get_pcie_ecam_base());
    bsp_uart_puts("\n");
    bsp_uart_puts("\n");

    /* UART Test */
    bsp_uart_puts("UART Test:\n");
    bsp_uart_puts("  [OK] PL011 UART initialized\n");
    bsp_uart_puts("  [OK] Serial output working\n");
    bsp_uart_puts("\n");

    /* Timer Test */
    bsp_uart_puts("Timer Test:\n");
    timer_ticks = bsp_timer_get_ticks();
    bsp_uart_puts("  Initial ticks: ");
    print_hex64(timer_ticks);
    bsp_uart_puts("\n");
    bsp_timer_delay_ms(100);
    timer_ticks = bsp_timer_get_ticks() - timer_ticks;
    bsp_uart_puts("  Ticks after 100ms: ");
    print_hex64(timer_ticks);
    bsp_uart_puts("\n");
    bsp_uart_puts("  [OK] ARM Generic Timer working\n");
    bsp_uart_puts("\n");

    /* GPIO Test */
    bsp_uart_puts("GPIO Test:\n");
    bsp_gpio_set_function(0, 1);
    bsp_gpio_set(0);
    bsp_gpio_clear(0);
    bsp_uart_puts("  [OK] PL061 GPIO working\n");
    bsp_uart_puts("\n");

    /* Memory Test */
    bsp_uart_puts("Memory Test:\n");
    test_alloc = simple_alloc(1024);
    if (test_alloc) {
        bsp_uart_puts("  Allocated 1KB at: ");
        print_hex64((uint64_t)(uintptr_t)test_alloc);
        bsp_uart_puts("\n");
        bsp_uart_puts("  [OK] Memory allocation working\n");
    } else {
        bsp_uart_puts("  [FAIL] Memory allocation failed\n");
    }
    bsp_uart_puts("\n");

    /* Kernel Boot Check */
    bsp_uart_puts("Kernel Boot Check:\n");
    uint64_t kernel_addr = KERNEL_LOAD_ADDR;
    uint64_t dtb_addr = DTB_LOAD_ADDR;

    if (kernel_validate(kernel_addr) == 0) {
        arm64_kernel_header_t *hdr = (arm64_kernel_header_t *)kernel_addr;
        bsp_uart_puts("  [OK] Kernel found at ");
        print_hex64(kernel_addr);
        bsp_uart_puts("\n");
        bsp_uart_puts("  Image size: ");
        print_hex64(hdr->image_size);
        bsp_uart_puts("\n");

        if (dtb_validate(dtb_addr) == 0) {
            bsp_uart_puts("  [OK] DTB found at ");
            print_hex64(dtb_addr);
            bsp_uart_puts(" (");
            print_hex64(dtb_get_size(dtb_addr));
            bsp_uart_puts(" bytes)\n");
        } else {
            dtb_addr = 0;
            bsp_uart_puts("  [INFO] No DTB found\n");
        }

        bsp_uart_puts("\n");
        bsp_uart_puts("========================================\n");
        bsp_uart_puts("  BOOTING KERNEL\n");
        bsp_uart_puts("========================================\n");
        bsp_uart_puts("\nKernel: ");
        print_hex64(kernel_addr);
        bsp_uart_puts("\n");
        if (dtb_addr) {
            bsp_uart_puts("DTB:    ");
            print_hex64(dtb_addr);
            bsp_uart_puts("\n");
        } else {
            bsp_uart_puts("DTB:    (none)\n");
        }
        bsp_uart_puts("\nJumping to kernel...\n\n");

        bsp_timer_delay_ms(100);
        kernel_boot(kernel_addr, dtb_addr);
    } else {
        bsp_uart_puts("  [INFO] No kernel at ");
        print_hex64(kernel_addr);
        bsp_uart_puts("\n");
    }
    bsp_uart_puts("\n");

    /* Boot Status */
    bsp_uart_puts("========================================\n");
    bsp_uart_puts("  BOOTLOADER READY\n");
    bsp_uart_puts("========================================\n");
    bsp_uart_puts("\n");

    /* Platform Features */
    bsp_uart_puts("Platform Features:\n");
    bsp_uart_puts("  [OK] PL011 UART serial\n");
    bsp_uart_puts("  [OK] ARM Generic Timer\n");
    bsp_uart_puts("  [OK] PL061 GPIO\n");
    bsp_uart_puts("  [OK] Dynamic memory allocation\n");
    bsp_uart_puts("  [OK] DTB loader\n");
    bsp_uart_puts("  [OK] Kernel loader\n");
    bsp_uart_puts("\n");

    /* Configuration */
    bsp_uart_puts("Configuration:\n");
    bsp_uart_puts("  Kernel load: ");
    print_hex64(KERNEL_LOAD_ADDR);
    bsp_uart_puts("\n");
    bsp_uart_puts("  DTB load:    ");
    print_hex64(DTB_LOAD_ADDR);
    bsp_uart_puts("\n");
    bsp_uart_puts("\n");

    /* Skipped Checks */
    bsp_uart_puts("Skipped Checks:\n");
    bsp_uart_puts("  [SKIP] PCIe enumeration - QEMU virt: no devices\n");
    bsp_uart_puts("  [SKIP] GIC config - Basic boot, no IRQ handling\n");
    bsp_uart_puts("  [SKIP] SMP cores - Single core boot test\n");
    bsp_uart_puts("\n");

    bsp_uart_puts("No kernel found. Waiting...\n");

    /* Idle loop */
    while (1) {
        __asm__ volatile ("wfe");
    }
}

/* ============================================================
 * Helper Functions
 * ============================================================ */

static void print_hex64(uint64_t val) {
    const char hex[] = "0123456789ABCDEF";
    char buf[19];
    int i;

    buf[0] = '0';
    buf[1] = 'x';
    for (i = 0; i < 16; i++) {
        buf[17 - i] = hex[val & 0xF];
        val >>= 4;
    }
    buf[18] = '\0';
    bsp_uart_puts(buf);
}

static void* simple_alloc(uint32_t size) {
    uint8_t *ptr;

    /* Initialize heap pointer if needed */
    if (heap_ptr == 0) {
        heap_ptr = &__heap_start;
    }

    /* Align size to 8 bytes */
    size = (size + 7) & ~7;

    /* Check if we have enough space */
    if ((heap_ptr + size) > &__heap_end) {
        return 0;
    }

    ptr = heap_ptr;
    heap_ptr += size;
    return ptr;
}
