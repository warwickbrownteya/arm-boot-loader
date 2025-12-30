/*
 * ARM Bootloader - Raspberry Pi 3 BSP Header
 * BCM2837 SoC - GPU-First Boot Architecture
 *
 * Note: GPU boots first and initializes ARM at 0x80000
 * Peripheral base: 0x3F000000 (Pi3) / 0xFE000000 (Pi4)
 */

#ifndef BSP_RASPI_H
#define BSP_RASPI_H

#include <stdint.h>

/* Platform identification - use common bsp.h enum value PLATFORM_RASPI3 */

/* BCM2837 Memory Map (Pi 3) */
#define RASPI_PERIPHERAL_BASE   0x3F000000
#define RASPI_RAM_BASE          0x00000000
#define RASPI_RAM_SIZE          0x40000000  /* 1 GB */

/* GPIO Controller */
#define RASPI_GPIO_BASE         (RASPI_PERIPHERAL_BASE + 0x200000)
#define RASPI_GPFSEL0           (RASPI_GPIO_BASE + 0x00)
#define RASPI_GPFSEL1           (RASPI_GPIO_BASE + 0x04)
#define RASPI_GPFSEL2           (RASPI_GPIO_BASE + 0x08)
#define RASPI_GPFSEL3           (RASPI_GPIO_BASE + 0x0C)
#define RASPI_GPFSEL4           (RASPI_GPIO_BASE + 0x10)
#define RASPI_GPFSEL5           (RASPI_GPIO_BASE + 0x14)
#define RASPI_GPSET0            (RASPI_GPIO_BASE + 0x1C)
#define RASPI_GPSET1            (RASPI_GPIO_BASE + 0x20)
#define RASPI_GPCLR0            (RASPI_GPIO_BASE + 0x28)
#define RASPI_GPCLR1            (RASPI_GPIO_BASE + 0x2C)
#define RASPI_GPLEV0            (RASPI_GPIO_BASE + 0x34)
#define RASPI_GPLEV1            (RASPI_GPIO_BASE + 0x38)
#define RASPI_GPPUD             (RASPI_GPIO_BASE + 0x94)
#define RASPI_GPPUDCLK0         (RASPI_GPIO_BASE + 0x98)
#define RASPI_GPPUDCLK1         (RASPI_GPIO_BASE + 0x9C)

/* PL011 UART (used by QEMU raspi3b) */
#define RASPI_UART0_BASE        (RASPI_PERIPHERAL_BASE + 0x201000)
#define RASPI_UART0_DR          (RASPI_UART0_BASE + 0x00)
#define RASPI_UART0_FR          (RASPI_UART0_BASE + 0x18)
#define RASPI_UART0_IBRD        (RASPI_UART0_BASE + 0x24)
#define RASPI_UART0_FBRD        (RASPI_UART0_BASE + 0x28)
#define RASPI_UART0_LCRH        (RASPI_UART0_BASE + 0x2C)
#define RASPI_UART0_CR          (RASPI_UART0_BASE + 0x30)
#define RASPI_UART0_ICR         (RASPI_UART0_BASE + 0x44)

/* PL011 flags */
#define UART0_FR_TXFF           (1 << 5)
#define UART0_FR_RXFE           (1 << 4)
#define UART0_CR_TXE            (1 << 8)
#define UART0_CR_RXE            (1 << 9)
#define UART0_CR_UARTEN         (1 << 0)
#define UART0_LCRH_FEN          (1 << 4)
#define UART0_LCRH_WLEN8        (3 << 5)

/* Mini UART (for real hardware, not QEMU) */
#define RASPI_AUX_BASE          (RASPI_PERIPHERAL_BASE + 0x215000)
#define RASPI_AUX_ENABLES       (RASPI_AUX_BASE + 0x04)
#define RASPI_AUX_MU_IO         (RASPI_AUX_BASE + 0x40)
#define RASPI_AUX_MU_IER        (RASPI_AUX_BASE + 0x44)
#define RASPI_AUX_MU_IIR        (RASPI_AUX_BASE + 0x48)
#define RASPI_AUX_MU_LCR        (RASPI_AUX_BASE + 0x4C)
#define RASPI_AUX_MU_MCR        (RASPI_AUX_BASE + 0x50)
#define RASPI_AUX_MU_LSR        (RASPI_AUX_BASE + 0x54)
#define RASPI_AUX_MU_MSR        (RASPI_AUX_BASE + 0x58)
#define RASPI_AUX_MU_SCRATCH    (RASPI_AUX_BASE + 0x5C)
#define RASPI_AUX_MU_CNTL       (RASPI_AUX_BASE + 0x60)
#define RASPI_AUX_MU_STAT       (RASPI_AUX_BASE + 0x64)
#define RASPI_AUX_MU_BAUD       (RASPI_AUX_BASE + 0x68)

/* LSR bits for Mini UART */
#define AUX_MU_LSR_TX_EMPTY     0x20
#define AUX_MU_LSR_RX_READY     0x01

/* ARM Timer (not system timer) */
#define RASPI_ARM_TIMER_BASE    (RASPI_PERIPHERAL_BASE + 0x00B400)
#define RASPI_ARM_TIMER_LOAD    (RASPI_ARM_TIMER_BASE + 0x00)
#define RASPI_ARM_TIMER_VALUE   (RASPI_ARM_TIMER_BASE + 0x04)
#define RASPI_ARM_TIMER_CTRL    (RASPI_ARM_TIMER_BASE + 0x08)
#define RASPI_ARM_TIMER_IRQCLR  (RASPI_ARM_TIMER_BASE + 0x0C)

/* System Timer (free-running 1MHz counter) */
#define RASPI_SYSTIMER_BASE     (RASPI_PERIPHERAL_BASE + 0x003000)
#define RASPI_SYSTIMER_CS       (RASPI_SYSTIMER_BASE + 0x00)
#define RASPI_SYSTIMER_CLO      (RASPI_SYSTIMER_BASE + 0x04)
#define RASPI_SYSTIMER_CHI      (RASPI_SYSTIMER_BASE + 0x08)
#define RASPI_SYSTIMER_C0       (RASPI_SYSTIMER_BASE + 0x0C)
#define RASPI_SYSTIMER_C1       (RASPI_SYSTIMER_BASE + 0x10)
#define RASPI_SYSTIMER_C2       (RASPI_SYSTIMER_BASE + 0x14)
#define RASPI_SYSTIMER_C3       (RASPI_SYSTIMER_BASE + 0x18)

/* Mailbox (GPU communication) */
#define RASPI_MAILBOX_BASE      (RASPI_PERIPHERAL_BASE + 0x00B880)
#define RASPI_MAILBOX_READ      (RASPI_MAILBOX_BASE + 0x00)
#define RASPI_MAILBOX_STATUS    (RASPI_MAILBOX_BASE + 0x18)
#define RASPI_MAILBOX_WRITE     (RASPI_MAILBOX_BASE + 0x20)

/* Mailbox status bits */
#define MAILBOX_FULL            0x80000000
#define MAILBOX_EMPTY           0x40000000

/* Mailbox channels */
#define MAILBOX_CHANNEL_POWER   0
#define MAILBOX_CHANNEL_FB      1
#define MAILBOX_CHANNEL_VUART   2
#define MAILBOX_CHANNEL_VCHIQ   3
#define MAILBOX_CHANNEL_LEDS    4
#define MAILBOX_CHANNEL_BTNS    5
#define MAILBOX_CHANNEL_TOUCH   6
#define MAILBOX_CHANNEL_COUNT   7
#define MAILBOX_CHANNEL_PROP    8

/* Activity LED GPIO */
#define RASPI_LED_GPIO          47  /* ACT LED on Pi 3 */

/* Register access macros */
#define MMIO_READ(reg)          (*(volatile uint32_t *)(reg))
#define MMIO_WRITE(reg, val)    (*(volatile uint32_t *)(reg) = (val))

/* bsp_info_t is defined in ../common/bsp.h - include it */
#include "../common/bsp.h"

/* Function prototypes */
void raspi_uart_init(void);
void raspi_uart_putc(char c);
void raspi_uart_puts(const char *s);
char raspi_uart_getc(void);
int raspi_uart_poll(void);

void raspi_timer_init(void);
uint64_t raspi_timer_get_ticks(void);
void raspi_timer_delay_us(uint32_t us);
void raspi_timer_delay_ms(uint32_t ms);

void raspi_gpio_init(void);
void raspi_gpio_set_function(uint32_t pin, uint32_t function);
void raspi_gpio_set(uint32_t pin);
void raspi_gpio_clear(uint32_t pin);
uint32_t raspi_gpio_read(uint32_t pin);

void raspi_led_on(void);
void raspi_led_off(void);
void raspi_led_blink(uint32_t count, uint32_t delay_ms);

uint32_t raspi_mailbox_call(uint32_t channel, uint32_t data);

void *raspi_malloc(uint32_t size);
void raspi_free(void *ptr);

const bsp_info_t *raspi_get_info(void);

/* Accessor functions for struct fields (to avoid GOT issues) */
uint64_t raspi_get_ram_base(void);
uint64_t raspi_get_ram_size(void);
uint64_t raspi_get_uart_base(void);
uint64_t raspi_get_gpio_base(void);

#endif /* BSP_RASPI_H */
