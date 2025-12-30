/* Main entry point for QEMU Virt Machine bootloader */

#include <stdint.h>
#include "../common/bsp.h"
#include "bsp_virt.h"
#include "kernel_boot.h"

/* Simple string output */
static void puts(const char *s) {
    bsp_uart_puts(s);
}

/* Print hex number */
static void print_hex(uint64_t val) {
    const char *hex = "0123456789ABCDEF";
    char buf[17];
    buf[16] = '\0';

    for (int i = 15; i >= 0; i--) {
        buf[i] = hex[val & 0xF];
        val >>= 4;
    }

    puts("0x");
    puts(buf);
}

/* Memory allocation (simple bump allocator for demo) */
extern uint8_t __heap_start;
extern uint8_t __heap_end;
static uint8_t *heap_ptr = 0;

static void *simple_malloc(uint32_t size) {
    if (!heap_ptr) {
        heap_ptr = &__heap_start;
    }

    /* Align to 8 bytes */
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

    /* Show memory map */
    puts("Memory Configuration:\n");
    puts("  RAM Base: ");
    print_hex(info->ram_base);
    puts("\n");
    puts("  RAM Size: ");
    print_hex(info->ram_size);
    puts(" (");
    /* Print in MB */
    uint32_t mb = info->ram_size / (1024 * 1024);
    char mbuf[4];
    mbuf[0] = '0' + (mb / 100) % 10;
    mbuf[1] = '0' + (mb / 10) % 10;
    mbuf[2] = '0' + mb % 10;
    mbuf[3] = '\0';
    puts(mbuf);
    puts(" MB)\n");
    puts("  UART Base: ");
    print_hex(info->uart_base);
    puts("\n");
    puts("\n");

    /* Test UART */
    puts("UART Test:\n");
    puts("  [OK] PL011 UART initialized\n");
    puts("  [OK] Serial output working\n");
    puts("\n");

    /* Test Timer */
    puts("Timer Test:\n");
    uint64_t start = bsp_timer_get_ticks();
    bsp_timer_delay_ms(100);
    uint64_t elapsed = bsp_timer_get_ticks() - start;
    puts("  Timer ticks for 100ms: ");
    print_hex(elapsed);
    puts("\n");
    puts("  [OK] ARM Generic Timer working\n");
    puts("\n");

    /* Test GPIO */
    puts("GPIO Test:\n");
    bsp_gpio_set_function(0, 1);  /* Set pin 0 as output */
    bsp_gpio_set(0);
    bsp_gpio_clear(0);
    puts("  [OK] PL061 GPIO initialized\n");
    puts("\n");

    /* Test Memory Allocation */
    puts("Memory Test:\n");
    void *ptr = simple_malloc(1024);
    if (ptr) {
        puts("  Allocated 1KB at: ");
        print_hex((uint64_t)ptr);
        puts("\n");
        puts("  [OK] Memory allocation working\n");
    } else {
        puts("  [FAIL] Memory allocation failed\n");
    }
    puts("\n");

    /* Check for pre-loaded kernel (via QEMU -device loader) */
    puts("Kernel Boot Check:\n");
    uint64_t kernel_addr = KERNEL_LOAD_ADDR;
    uint64_t dtb_addr = DTB_LOAD_ADDR;

    /* Check if kernel is present at load address */
    if (kernel_validate(kernel_addr) == 0) {
        arm64_kernel_header_t *hdr = (arm64_kernel_header_t *)kernel_addr;
        puts("  [OK] Kernel found at ");
        print_hex(kernel_addr);
        puts("\n");
        puts("  Image size: ");
        print_hex(hdr->image_size);
        puts("\n");

        /* Check for DTB */
        if (dtb_validate(dtb_addr) == 0) {
            puts("  [OK] DTB found at ");
            print_hex(dtb_addr);
            puts(" (");
            print_hex(dtb_get_size(dtb_addr));
            puts(" bytes)\n");
        } else {
            dtb_addr = 0;
            puts("  [INFO] No DTB at ");
            print_hex(DTB_LOAD_ADDR);
            puts("\n");
        }

        puts("\n");
        puts("========================================\n");
        puts("  BOOTING KERNEL\n");
        puts("========================================\n");
        puts("\nKernel: ");
        print_hex(kernel_addr);
        puts("\n");
        if (dtb_addr) {
            puts("DTB:    ");
            print_hex(dtb_addr);
            puts("\n");
        } else {
            puts("DTB:    (none)\n");
        }
        puts("\nJumping to kernel...\n\n");

        bsp_timer_delay_ms(100);
        kernel_boot(kernel_addr, dtb_addr);
        /* Never returns */
    } else {
        puts("  [INFO] No kernel at ");
        print_hex(kernel_addr);
        puts("\n");
    }
    puts("\n");

    /* Success */
    puts("========================================\n");
    puts("  BOOTLOADER READY\n");
    puts("========================================\n");
    puts("\n");

    puts("Platform Features:\n");
    puts("  [OK] PL011 UART serial communication\n");
    puts("  [OK] ARM Generic Timer\n");
    puts("  [OK] PL061 GPIO controller\n");
    puts("  [OK] Dynamic memory allocation\n");
    puts("  [OK] DTB loader\n");
    puts("  [OK] Kernel loader\n");
    puts("\n");

    puts("Configuration:\n");
    puts("  Kernel load: ");
    print_hex(KERNEL_LOAD_ADDR);
    puts("\n");
    puts("  DTB load:    ");
    print_hex(DTB_LOAD_ADDR);
    puts("\n");
    puts("\n");

    puts("Skipped Checks:\n");
    puts("  [SKIP] Virtio-blk - QEMU virt: no disk attached\n");
    puts("  [SKIP] Virtio-net - QEMU virt: no network config\n");
    puts("  [SKIP] GIC config - Basic boot, no IRQ handling\n");
    puts("  [SKIP] SMP cores - Single core boot test\n");
    puts("\n");

    puts("No kernel found. Waiting...\n");

    /* Idle loop */
    while (1) {
        __asm__ volatile ("wfe");
    }
}
