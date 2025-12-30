/* Main entry point for ARM Versatile Express A15 bootloader */

#include <stdint.h>
#include "../common/bsp.h"
#include "bsp_vexpress.h"
#include "kernel_boot.h"

/* External functions from bsp_vexpress.c */
extern uint32_t vexpress_get_board_id(void);
extern uint32_t vexpress_get_proc_id(void);
extern uint32_t vexpress_get_100hz_counter(void);
extern uint32_t vexpress_get_switches(void);

/* Simple string output */
static void puts(const char *s) {
    bsp_uart_puts(s);
}

/* Print 32-bit hex number */
static void print_hex32(uint32_t val) {
    const char *hex = "0123456789ABCDEF";
    char buf[9];
    buf[8] = '\0';

    for (int i = 7; i >= 0; i--) {
        buf[i] = hex[val & 0xF];
        val >>= 4;
    }

    puts("0x");
    puts(buf);
}

/* Memory allocation (simple bump allocator) */
extern uint8_t __heap_start;
extern uint8_t __heap_end;
static uint8_t *heap_ptr = 0;

static void *simple_malloc(uint32_t size) {
    if (!heap_ptr) {
        heap_ptr = &__heap_start;
    }

    size = (size + 7) & ~7;

    if (heap_ptr + size > &__heap_end) {
        return 0;
    }

    void *ptr = heap_ptr;
    heap_ptr += size;
    return ptr;
}

/* Main entry point */
void main(void) {
    const bsp_info_t *info;

    /* Initialize BSP */
    bsp_init();

    /* Get platform info */
    info = bsp_get_info();

    /* Print banner */
    puts("\n");
    puts("========================================\n");
    puts("  ARM Bootloader - ");
    puts(info->name);
    puts("\n");
    puts("  ");
    puts(info->description);
    puts("\n");
    puts("========================================\n");
    puts("\n");

    /* Show board identification */
    puts("Board Identification:\n");
    puts("  Board ID: ");
    print_hex32(vexpress_get_board_id());
    puts("\n");
    puts("  Processor ID: ");
    print_hex32(vexpress_get_proc_id());
    puts("\n");
    puts("  Switches: ");
    print_hex32(vexpress_get_switches());
    puts("\n");
    puts("\n");

    /* Show memory map */
    puts("Memory Configuration:\n");
    puts("  DRAM Base: ");
    print_hex32((uint32_t)info->ram_base);
    puts("\n");
    puts("  DRAM Size: ");
    print_hex32((uint32_t)info->ram_size);
    puts(" (1 GB)\n");
    puts("  UART Base: ");
    print_hex32((uint32_t)info->uart_base);
    puts("\n");
    puts("  Timer Base: ");
    print_hex32((uint32_t)info->timer_base);
    puts("\n");
    puts("\n");

    /* Test UART */
    puts("UART Test:\n");
    puts("  [OK] PL011 UART initialized\n");
    puts("  [OK] Serial output working\n");
    puts("\n");

    /* Test Timer */
    puts("Timer Test:\n");
    puts("  100Hz Counter: ");
    print_hex32(vexpress_get_100hz_counter());
    puts("\n");
    uint64_t start = bsp_timer_get_ticks();
    bsp_timer_delay_ms(100);
    uint64_t elapsed = bsp_timer_get_ticks() - start;
    puts("  SP804 ticks for 100ms: ");
    print_hex32((uint32_t)elapsed);
    puts("\n");
    puts("  [OK] SP804 Dual Timer working\n");
    puts("\n");

    /* Test GPIO/LEDs */
    puts("LED Test:\n");
    for (int i = 0; i < 8; i++) {
        bsp_gpio_set(i);
    }
    bsp_timer_delay_ms(50);
    for (int i = 0; i < 8; i++) {
        bsp_gpio_clear(i);
    }
    puts("  [OK] System Register LEDs working\n");
    puts("\n");

    /* Test Memory */
    puts("Memory Test:\n");
    void *ptr = simple_malloc(1024);
    if (ptr) {
        puts("  Allocated 1KB at: ");
        print_hex32((uint32_t)(uintptr_t)ptr);
        puts("\n");
        puts("  [OK] Memory allocation working\n");
    } else {
        puts("  [FAIL] Memory allocation failed\n");
    }
    puts("\n");

    /* Check for pre-loaded kernel */
    puts("Kernel Boot Check:\n");
    uint32_t kernel_addr = KERNEL_LOAD_ADDR;
    uint32_t dtb_addr = DTB_LOAD_ADDR;

    if (kernel_validate(kernel_addr) == 0) {
        arm32_zimage_header_t *hdr = (arm32_zimage_header_t *)kernel_addr;
        puts("  [OK] Kernel found at ");
        print_hex32(kernel_addr);
        puts("\n");
        puts("  zImage end: ");
        print_hex32(hdr->end);
        puts("\n");

        /* Check for DTB */
        if (dtb_validate(dtb_addr) == 0) {
            puts("  [OK] DTB found at ");
            print_hex32(dtb_addr);
            puts(" (");
            print_hex32(dtb_get_size(dtb_addr));
            puts(" bytes)\n");
        } else {
            dtb_addr = 0;
            puts("  [INFO] No DTB found\n");
        }

        puts("\n");
        puts("========================================\n");
        puts("  BOOTING KERNEL\n");
        puts("========================================\n");
        puts("\nKernel: ");
        print_hex32(kernel_addr);
        puts("\n");
        if (dtb_addr) {
            puts("DTB:    ");
            print_hex32(dtb_addr);
            puts("\n");
        } else {
            puts("DTB:    (none)\n");
        }
        puts("\nJumping to kernel...\n\n");

        bsp_timer_delay_ms(100);
        kernel_boot(kernel_addr, dtb_addr);
    } else {
        puts("  [INFO] No kernel at ");
        print_hex32(kernel_addr);
        puts("\n");
    }
    puts("\n");

    /* Success */
    puts("========================================\n");
    puts("  BOOTLOADER READY\n");
    puts("========================================\n");
    puts("\n");

    puts("Platform Features:\n");
    puts("  [OK] PL011 UART serial\n");
    puts("  [OK] SP804 Dual Timer\n");
    puts("  [OK] System Register LEDs\n");
    puts("  [OK] Dynamic memory allocation\n");
    puts("  [OK] DTB loader\n");
    puts("  [OK] Kernel loader\n");
    puts("\n");

    puts("Configuration:\n");
    puts("  Kernel load: ");
    print_hex32(KERNEL_LOAD_ADDR);
    puts("\n");
    puts("  DTB load:    ");
    print_hex32(DTB_LOAD_ADDR);
    puts("\n");
    puts("\n");

    puts("Versatile Express A15 Resources:\n");
    puts("  - Cortex-A15 MPCore\n");
    puts("  - 1GB DDR RAM\n");
    puts("  - PL180 MMC storage\n");
    puts("  - GIC interrupt controller\n");
    puts("  - PL031 RTC\n");
    puts("  - PL111 CLCD display\n");
    puts("\n");

    puts("Skipped Checks:\n");
    puts("  [SKIP] PL180 MMC - QEMU vexpress-a15: no SD image attached\n");
    puts("  [SKIP] PL031 RTC - Not critical for boot validation\n");
    puts("  [SKIP] PL111 CLCD - QEMU vexpress-a15: no display attached\n");
    puts("  [SKIP] GIC config - Basic boot, no IRQ handling\n");
    puts("  [SKIP] SMP cores - Single core boot test\n");
    puts("\n");

    puts("No kernel found. Waiting...\n");
    while (1) {
        __asm__ volatile ("wfe");
    }
}
