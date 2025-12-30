#ifndef HARDWARE_H
#define HARDWARE_H

#include <stdint.h>

/* Platform types */
typedef enum {
    PLATFORM_UNKNOWN,
    PLATFORM_VIRT,     /* QEMU virt machine */
    PLATFORM_BCM2835,  /* Raspberry Pi 0, 1 */
    PLATFORM_BCM2837,  /* Raspberry Pi 2, 3 */
    PLATFORM_BCM2711   /* Raspberry Pi 4 */
} platform_t;

/* Platform detection */
void hardware_detect_platform(void);
platform_t hardware_get_platform(void);

/* Runtime base address getters */
uintptr_t get_uart_base(void);
uintptr_t get_gpio_base(void);
uintptr_t get_timer_base(void);
uintptr_t get_mailbox_base(void);

#endif /* HARDWARE_H */
