/*
 * ARM Bootloader - Raspberry Pi 3 BSP Implementation
 * BCM2837 SoC - GPU-First Boot Architecture
 */

#include "bsp_raspi.h"
#include "../common/bsp.h"  /* For bsp_err_t and common interface */
#include <stddef.h>  /* For NULL */

/* Error codes (local copy to avoid header conflicts) */
typedef enum {
    RASPI_OK = 0,
    RASPI_ERR_TIMEOUT = -1,
    RASPI_ERR_INVALID = -3
} raspi_err_t;

/* Timeout values */
#define RASPI_TIMEOUT_INFINITE  0xFFFFFFFF

/* Timer frequency (BCM System Timer runs at 1MHz) */
static const uint32_t timer_freq = 1000000;

/* BSP Info - constant data */
static const bsp_info_t raspi_info = {
    .id = PLATFORM_RASPI3,
    .name = "Raspberry Pi 3",
    .description = "BCM2837 - Quad Cortex-A53 @ 1.2GHz",
    .uart_base = RASPI_AUX_BASE + 0x40,
    .timer_base = RASPI_SYSTIMER_BASE,
    .gpio_base = RASPI_GPIO_BASE,
    .ram_base = RASPI_RAM_BASE,
    .ram_size = RASPI_RAM_SIZE,
    .cpu_freq_hz = 1200000000
};

/* Heap management */
extern char _heap_start;
extern char _heap_end;
static char *heap_ptr = 0;

/* ========================================================================= */
/* UART Functions (PL011 for QEMU / Mini UART for real hardware)             */
/* ========================================================================= */

void raspi_uart_init(void) {
    /* Use PL011 UART for QEMU compatibility */
    /* QEMU's raspi3b uses PL011 at 0x3F201000, not Mini UART */

    /* Clear pending interrupts */
    MMIO_WRITE(RASPI_UART0_ICR, 0x7FF);

    /* Enable UART with TX/RX */
    MMIO_WRITE(RASPI_UART0_CR, UART0_CR_UARTEN | UART0_CR_TXE | UART0_CR_RXE);
}

/* Timeout-aware UART putc */
raspi_err_t raspi_uart_putc_timeout(char c, uint32_t timeout_ms) {
    uint64_t start = raspi_timer_get_ticks();
    uint64_t timeout_ticks;

    /* System timer runs at 1MHz, so ticks = microseconds */
    if (timeout_ms == RASPI_TIMEOUT_INFINITE) {
        timeout_ticks = UINT64_MAX;
    } else {
        timeout_ticks = (uint64_t)timeout_ms * 1000;
    }

    /* Wait for TX FIFO to have space (PL011), with timeout */
    while (MMIO_READ(RASPI_UART0_FR) & UART0_FR_TXFF) {
        if ((raspi_timer_get_ticks() - start) >= timeout_ticks) {
            return RASPI_ERR_TIMEOUT;
        }
    }

    MMIO_WRITE(RASPI_UART0_DR, c);
    return RASPI_OK;
}

/* Timeout-aware UART getc */
raspi_err_t raspi_uart_getc_timeout(char *c, uint32_t timeout_ms) {
    uint64_t start = raspi_timer_get_ticks();
    uint64_t timeout_ticks;

    if (c == NULL) {
        return RASPI_ERR_INVALID;
    }

    if (timeout_ms == RASPI_TIMEOUT_INFINITE) {
        timeout_ticks = UINT64_MAX;
    } else {
        timeout_ticks = (uint64_t)timeout_ms * 1000;
    }

    /* Wait for RX FIFO to have data (PL011), with timeout */
    while (MMIO_READ(RASPI_UART0_FR) & UART0_FR_RXFE) {
        if ((raspi_timer_get_ticks() - start) >= timeout_ticks) {
            return RASPI_ERR_TIMEOUT;
        }
    }

    *c = (char)(MMIO_READ(RASPI_UART0_DR) & 0xFF);
    return RASPI_OK;
}

/* Timeout-aware UART puts */
raspi_err_t raspi_uart_puts_timeout(const char *s, uint32_t timeout_ms) {
    raspi_err_t err;

    if (s == NULL) {
        return RASPI_ERR_INVALID;
    }

    while (*s) {
        if (*s == '\n') {
            err = raspi_uart_putc_timeout('\r', timeout_ms);
            if (err != RASPI_OK) return err;
        }
        err = raspi_uart_putc_timeout(*s++, timeout_ms);
        if (err != RASPI_OK) return err;
    }
    return RASPI_OK;
}

/* Blocking UART putc (backwards compatible) */
void raspi_uart_putc(char c) {
    raspi_uart_putc_timeout(c, RASPI_TIMEOUT_INFINITE);
}

/* Blocking UART puts (backwards compatible) */
void raspi_uart_puts(const char *s) {
    raspi_uart_puts_timeout(s, RASPI_TIMEOUT_INFINITE);
}

/* Blocking UART getc (backwards compatible) */
char raspi_uart_getc(void) {
    char c;
    raspi_uart_getc_timeout(&c, RASPI_TIMEOUT_INFINITE);
    return c;
}

int raspi_uart_poll(void) {
    /* Check if RX FIFO has data (PL011) */
    return !(MMIO_READ(RASPI_UART0_FR) & UART0_FR_RXFE);
}

/* ========================================================================= */
/* Timer Functions (System Timer - 1MHz free-running counter)               */
/* ========================================================================= */

void raspi_timer_init(void) {
    /* System timer is always running, no init needed */
}

uint64_t raspi_timer_get_ticks(void) {
    uint32_t hi, lo;

    /* Read both halves atomically (check for overflow) */
    do {
        hi = MMIO_READ(RASPI_SYSTIMER_CHI);
        lo = MMIO_READ(RASPI_SYSTIMER_CLO);
    } while (hi != MMIO_READ(RASPI_SYSTIMER_CHI));

    return ((uint64_t)hi << 32) | lo;
}

void raspi_timer_delay_us(uint32_t us) {
    uint64_t start = raspi_timer_get_ticks();
    while ((raspi_timer_get_ticks() - start) < us) {
        /* Spin - timer runs at 1MHz so ticks = microseconds */
    }
}

void raspi_timer_delay_ms(uint32_t ms) {
    raspi_timer_delay_us(ms * 1000);
}

uint32_t raspi_timer_get_freq(void) {
    return timer_freq;
}

/* ========================================================================= */
/* GPIO Functions                                                            */
/* ========================================================================= */

void raspi_gpio_init(void) {
    /* GPIO is always available, configure activity LED */
    raspi_gpio_set_function(RASPI_LED_GPIO, 1);  /* Output */
}

void raspi_gpio_set_function(uint32_t pin, uint32_t function) {
    volatile uint32_t *gpfsel;
    uint32_t shift;
    uint32_t val;

    if (pin >= 54) return;  /* Invalid pin */

    /* Each GPFSEL register handles 10 pins, 3 bits each */
    gpfsel = (volatile uint32_t *)(uintptr_t)(RASPI_GPFSEL0 + (pin / 10) * 4);
    shift = (pin % 10) * 3;

    val = *gpfsel;
    val &= ~(7 << shift);
    val |= ((function & 7) << shift);
    *gpfsel = val;
}

void raspi_gpio_set(uint32_t pin) {
    if (pin < 32) {
        MMIO_WRITE(RASPI_GPSET0, 1 << pin);
    } else if (pin < 54) {
        MMIO_WRITE(RASPI_GPSET1, 1 << (pin - 32));
    }
}

void raspi_gpio_clear(uint32_t pin) {
    if (pin < 32) {
        MMIO_WRITE(RASPI_GPCLR0, 1 << pin);
    } else if (pin < 54) {
        MMIO_WRITE(RASPI_GPCLR1, 1 << (pin - 32));
    }
}

uint32_t raspi_gpio_read(uint32_t pin) {
    uint32_t val;

    if (pin < 32) {
        val = MMIO_READ(RASPI_GPLEV0);
        return (val >> pin) & 1;
    } else if (pin < 54) {
        val = MMIO_READ(RASPI_GPLEV1);
        return (val >> (pin - 32)) & 1;
    }
    return 0;
}

/* ========================================================================= */
/* LED Functions                                                             */
/* ========================================================================= */

void raspi_led_on(void) {
    raspi_gpio_clear(RASPI_LED_GPIO);  /* Active low on Pi 3 */
}

void raspi_led_off(void) {
    raspi_gpio_set(RASPI_LED_GPIO);
}

void raspi_led_blink(uint32_t count, uint32_t delay_ms) {
    for (uint32_t i = 0; i < count; i++) {
        raspi_led_on();
        raspi_timer_delay_ms(delay_ms);
        raspi_led_off();
        raspi_timer_delay_ms(delay_ms);
    }
}

/* ========================================================================= */
/* Mailbox Functions (GPU Communication)                                     */
/* ========================================================================= */

uint32_t raspi_mailbox_call(uint32_t channel, uint32_t data) {
    uint32_t msg = (data & ~0xF) | (channel & 0xF);

    /* Wait for mailbox to be ready for write */
    while (MMIO_READ(RASPI_MAILBOX_STATUS) & MAILBOX_FULL) {
        /* Spin */
    }

    /* Write message */
    MMIO_WRITE(RASPI_MAILBOX_WRITE, msg);

    /* Wait for response */
    while (1) {
        while (MMIO_READ(RASPI_MAILBOX_STATUS) & MAILBOX_EMPTY) {
            /* Spin */
        }

        uint32_t response = MMIO_READ(RASPI_MAILBOX_READ);
        if ((response & 0xF) == channel) {
            return response & ~0xF;
        }
    }
}

/* ========================================================================= */
/* Memory Allocation                                                         */
/* ========================================================================= */

void *raspi_malloc(uint32_t size) {
    char *result;

    if (heap_ptr == 0) {
        heap_ptr = &_heap_start;
    }

    /* Align to 8 bytes */
    size = (size + 7) & ~7;

    if (heap_ptr + size > &_heap_end) {
        return 0;  /* Out of memory */
    }

    result = heap_ptr;
    heap_ptr += size;

    return result;
}

void raspi_free(void *ptr) {
    /* Simple bump allocator - no free */
    (void)ptr;
}

/* ========================================================================= */
/* BSP Info                                                                  */
/* ========================================================================= */

const bsp_info_t *raspi_get_info(void) {
    return &raspi_info;
}

/* Accessor functions to avoid GOT issues */
uint64_t raspi_get_ram_base(void) {
    return RASPI_RAM_BASE;
}

uint64_t raspi_get_ram_size(void) {
    return RASPI_RAM_SIZE;
}

uint64_t raspi_get_uart_base(void) {
    return RASPI_AUX_BASE + 0x40;
}

uint64_t raspi_get_gpio_base(void) {
    return RASPI_GPIO_BASE;
}

/* ========================================================================= */
/* Common BSP Interface Wrappers (for unified build)                         */
/* ========================================================================= */

void bsp_init(void) {
    raspi_uart_init();
    raspi_timer_init();
    raspi_gpio_init();
}

const bsp_info_t *bsp_get_info(void) {
    return raspi_get_info();
}

void bsp_uart_init(void) {
    raspi_uart_init();
}

void bsp_uart_putc(char c) {
    raspi_uart_putc(c);
}

char bsp_uart_getc(void) {
    return raspi_uart_getc();
}

int bsp_uart_tstc(void) {
    return raspi_uart_poll();
}

void bsp_uart_puts(const char *s) {
    raspi_uart_puts(s);
}

bsp_err_t bsp_uart_putc_timeout(char c, uint32_t timeout_ms) {
    return (bsp_err_t)raspi_uart_putc_timeout(c, timeout_ms);
}

bsp_err_t bsp_uart_getc_timeout(char *c, uint32_t timeout_ms) {
    return (bsp_err_t)raspi_uart_getc_timeout(c, timeout_ms);
}

bsp_err_t bsp_uart_puts_timeout(const char *s, uint32_t timeout_ms) {
    return (bsp_err_t)raspi_uart_puts_timeout(s, timeout_ms);
}

void bsp_timer_init(void) {
    raspi_timer_init();
}

uint64_t bsp_timer_get_ticks(void) {
    return raspi_timer_get_ticks();
}

uint32_t bsp_timer_get_freq(void) {
    return raspi_timer_get_freq();
}

void bsp_timer_delay_us(uint32_t us) {
    raspi_timer_delay_us(us);
}

void bsp_timer_delay_ms(uint32_t ms) {
    raspi_timer_delay_ms(ms);
}

void bsp_gpio_init(void) {
    raspi_gpio_init();
}

void bsp_gpio_set_function(uint8_t pin, uint8_t function) {
    raspi_gpio_set_function((uint32_t)pin, (uint32_t)function);
}

void bsp_gpio_set(uint8_t pin) {
    raspi_gpio_set((uint32_t)pin);
}

void bsp_gpio_clear(uint8_t pin) {
    raspi_gpio_clear((uint32_t)pin);
}

/* ============================================================
 * Network Driver Stubs
 * ============================================================ */

#include "../common/net.h"

/* Raspberry Pi 3 has USB Ethernet (LAN9514) which requires USB driver */
static mac_addr_t raspi_mac = {{ 0xB8, 0x27, 0xEB, 0x12, 0x34, 0x56 }};

int bsp_net_init(void) {
    return 0;
}

int bsp_net_link_up(void) {
    return 1;
}

void bsp_net_get_mac(mac_addr_t *mac) {
    for (int i = 0; i < 6; i++) {
        mac->addr[i] = raspi_mac.addr[i];
    }
}

int bsp_net_send(const uint8_t *data, size_t len) {
    (void)data;
    (void)len;
    return 0;
}

int bsp_net_recv(uint8_t *data, size_t maxlen) {
    (void)data;
    (void)maxlen;
    return 0;
}

uint32_t bsp_net_get_time_ms(void) {
    return (uint32_t)(bsp_timer_get_ticks() * 1000 / bsp_timer_get_freq());
}

/* ============================================================
 * Storage Driver Implementation
 * ============================================================ */

/* Raspberry Pi uses the EMMC controller via sd.c */

#include "../common/storage.h"

/* External declarations from sd.c */
extern int sd_init(void);
extern int sd_is_initialized(void);
extern int sd_read_sector(uint32_t sector, uint8_t *buffer);
extern int sd_read_sectors(uint32_t start_sector, uint32_t count, uint8_t *buffer);

/* Storage state */
static int raspi_sd_initialized = 0;

int bsp_storage_init(int device) {
    if (device != 0) {
        return -1;  /* Only device 0 supported */
    }

    if (sd_init() == 0) {
        raspi_sd_initialized = 1;
        return 0;
    }

    return -1;
}

int bsp_storage_present(int device) {
    if (device != 0) {
        return 0;
    }

    return sd_is_initialized();
}

int bsp_storage_info(int device, storage_info_t *info) {
    if (device != 0 || !raspi_sd_initialized) {
        return -1;
    }

    info->type = STORAGE_TYPE_SDHC;  /* Assume SDHC */
    info->initialized = 1;
    info->block_size = 512;
    info->total_blocks = 0;  /* Unknown without reading CSD */
    info->capacity_mb = 0;
    info->vendor[0] = '\0';
    info->product[0] = '\0';
    info->serial[0] = '\0';

    return 0;
}

int bsp_storage_read(int device, uint64_t block, uint32_t count, uint8_t *buffer) {
    if (device != 0 || !raspi_sd_initialized) {
        return -1;
    }

    return sd_read_sectors((uint32_t)block, count, buffer);
}

int bsp_storage_write(int device, uint64_t block, uint32_t count, const uint8_t *buffer) {
    (void)device;
    (void)block;
    (void)count;
    (void)buffer;
    /* Write not implemented in sd.c */
    return -1;
}
