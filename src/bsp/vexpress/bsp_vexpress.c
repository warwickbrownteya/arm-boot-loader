/* ARM Versatile Express A15 BSP Implementation (ARMv7-A 32-bit) */

#include <stdint.h>
#include "../common/bsp.h"
#include "bsp_vexpress.h"

/* BSP Information */
static const bsp_info_t vexpress_bsp_info = {
    .id          = PLATFORM_VEXPRESS_A15,
    .name        = "Versatile Express A15",
    .description = "ARM Versatile Express for Cortex-A15",
    .uart_base   = VEXPRESS_SERIAL_BASE,
    .timer_base  = VEXPRESS_TIMER_BASE,
    .gpio_base   = VEXPRESS_SYSREG_BASE,  /* Use sysreg LEDs as GPIO */
    .ram_base    = VEXPRESS_DRAM_BASE,
    .ram_size    = VEXPRESS_DRAM_SIZE,
    .cpu_freq_hz = 1000000  /* SP804 runs at 1MHz */
};

/* ============================================================
 * MMIO Helpers - uses bsp_addr_t from common header
 * ============================================================ */

static inline void mmio_write(bsp_addr_t reg, uint32_t data) {
    bsp_dsb();
    *(volatile uint32_t*)(uintptr_t)reg = data;
    bsp_dmb();
}

static inline uint32_t mmio_read(bsp_addr_t reg) {
    bsp_dmb();
    return *(volatile uint32_t*)(uintptr_t)reg;
}

/* ============================================================
 * BSP Core Functions
 * ============================================================ */

void bsp_init(void) {
    bsp_uart_init();
    bsp_timer_init();
    bsp_gpio_init();
}

const bsp_info_t* bsp_get_info(void) {
    return &vexpress_bsp_info;
}

/* Timer frequency constant (SP804 runs at 1MHz) */
static const uint32_t timer_freq = 1000000;

/* ============================================================
 * PL011 UART Implementation
 * ============================================================ */

void bsp_uart_init(void) {
    bsp_addr_t base = VEXPRESS_SERIAL_BASE;

    /* QEMU's PL011 is pre-configured, just ensure it's enabled.
     * Skip full initialization to avoid breaking QEMU's config.
     */

    /* Clear any pending interrupts */
    mmio_write(base + PL011_ICR, 0x7FF);

    /* Disable all interrupts */
    mmio_write(base + PL011_IMSC, 0);

    /* Ensure UART is enabled with TX/RX */
    mmio_write(base + PL011_CR, PL011_CR_UARTEN | PL011_CR_TXE | PL011_CR_RXE);
}

/* Timeout-aware UART putc */
bsp_err_t bsp_uart_putc_timeout(char c, uint32_t timeout_ms) {
    bsp_addr_t base = VEXPRESS_SERIAL_BASE;
    uint64_t start = bsp_timer_get_ticks();
    uint64_t timeout_ticks;

    /* SP804 runs at 1MHz, so 1000 ticks = 1ms */
    if (timeout_ms == BSP_TIMEOUT_INFINITE) {
        timeout_ticks = UINT64_MAX;
    } else {
        timeout_ticks = (uint64_t)timeout_ms * 1000;
    }

    /* Wait until TX FIFO not full, with timeout */
    while (mmio_read(base + PL011_FR) & PL011_FR_TXFF) {
        if ((bsp_timer_get_ticks() - start) >= timeout_ticks) {
            return BSP_ERR_TIMEOUT;
        }
    }

    /* Write character */
    mmio_write(base + PL011_DR, (uint32_t)c);
    return BSP_OK;
}

/* Timeout-aware UART getc */
bsp_err_t bsp_uart_getc_timeout(char *c, uint32_t timeout_ms) {
    bsp_addr_t base = VEXPRESS_SERIAL_BASE;
    uint64_t start = bsp_timer_get_ticks();
    uint64_t timeout_ticks;

    if (c == NULL) {
        return BSP_ERR_INVALID;
    }

    if (timeout_ms == BSP_TIMEOUT_INFINITE) {
        timeout_ticks = UINT64_MAX;
    } else {
        timeout_ticks = (uint64_t)timeout_ms * 1000;
    }

    /* Wait until RX FIFO not empty, with timeout */
    while (mmio_read(base + PL011_FR) & PL011_FR_RXFE) {
        if ((bsp_timer_get_ticks() - start) >= timeout_ticks) {
            return BSP_ERR_TIMEOUT;
        }
    }

    *c = (char)(mmio_read(base + PL011_DR) & 0xFF);
    return BSP_OK;
}

/* Timeout-aware UART puts */
bsp_err_t bsp_uart_puts_timeout(const char *s, uint32_t timeout_ms) {
    bsp_err_t err;

    if (s == NULL) {
        return BSP_ERR_INVALID;
    }

    while (*s) {
        if (*s == '\n') {
            err = bsp_uart_putc_timeout('\r', timeout_ms);
            if (err != BSP_OK) return err;
        }
        err = bsp_uart_putc_timeout(*s++, timeout_ms);
        if (err != BSP_OK) return err;
    }
    return BSP_OK;
}

/* Blocking UART putc (backwards compatible) */
void bsp_uart_putc(char c) {
    bsp_uart_putc_timeout(c, BSP_TIMEOUT_INFINITE);
}

/* Blocking UART getc (backwards compatible) */
char bsp_uart_getc(void) {
    char c;
    bsp_uart_getc_timeout(&c, BSP_TIMEOUT_INFINITE);
    return c;
}

int bsp_uart_tstc(void) {
    bsp_addr_t base = VEXPRESS_SERIAL_BASE;
    return !(mmio_read(base + PL011_FR) & PL011_FR_RXFE);
}

/* Blocking UART puts (backwards compatible) */
void bsp_uart_puts(const char *s) {
    bsp_uart_puts_timeout(s, BSP_TIMEOUT_INFINITE);
}

/* ============================================================
 * SP804 Dual Timer Implementation
 * ============================================================ */

void bsp_timer_init(void) {
    bsp_addr_t base = VEXPRESS_TIMER_BASE;

    /* Disable timer 1 */
    mmio_write(base + SP804_TIMER1_CONTROL, 0);

    /* Load maximum value for free-running counter */
    mmio_write(base + SP804_TIMER1_LOAD, 0xFFFFFFFF);

    /* Configure: 32-bit, free-running (no periodic), no interrupt, prescale /1 */
    uint32_t ctrl = SP804_CTRL_32BIT | SP804_CTRL_PRESCALE_1;
    mmio_write(base + SP804_TIMER1_CONTROL, ctrl);

    /* Enable timer */
    mmio_write(base + SP804_TIMER1_CONTROL, ctrl | SP804_CTRL_ENABLE);
}

uint64_t bsp_timer_get_ticks(void) {
    bsp_addr_t base = VEXPRESS_TIMER_BASE;

    /* SP804 counts down, so invert to get increasing ticks */
    uint32_t val = mmio_read(base + SP804_TIMER1_VALUE);
    return (uint64_t)(0xFFFFFFFF - val);
}

void bsp_timer_delay_us(uint32_t us) {
    /* SP804 runs at 1MHz, so 1 tick = 1 microsecond */
    uint64_t start = bsp_timer_get_ticks();
    uint64_t target = (uint64_t)us;

    while ((bsp_timer_get_ticks() - start) < target);
}

void bsp_timer_delay_ms(uint32_t ms) {
    bsp_timer_delay_us(ms * 1000);
}

uint32_t bsp_timer_get_freq(void) {
    return timer_freq;
}

/* ============================================================
 * GPIO Implementation (using System Register LEDs)
 * ============================================================ */

static uint32_t led_state = 0;

void bsp_gpio_init(void) {
    /* Clear all LEDs initially */
    led_state = 0;
    mmio_write(VEXPRESS_SYSREG_BASE + SYSREG_LED, 0);
}

void bsp_gpio_set_function(uint8_t pin, uint8_t function) {
    /* LEDs are always outputs, nothing to configure */
    (void)pin;
    (void)function;
}

void bsp_gpio_set(uint8_t pin) {
    if (pin > 7) return;  /* 8 LEDs available */

    led_state |= (1 << pin);
    mmio_write(VEXPRESS_SYSREG_BASE + SYSREG_LED, led_state);
}

void bsp_gpio_clear(uint8_t pin) {
    if (pin > 7) return;

    led_state &= ~(1 << pin);
    mmio_write(VEXPRESS_SYSREG_BASE + SYSREG_LED, led_state);
}

/* ============================================================
 * Additional Versatile Express Functions
 * ============================================================ */

/* Read board ID */
uint32_t vexpress_get_board_id(void) {
    return mmio_read(VEXPRESS_SYSREG_BASE + SYSREG_ID);
}

/* Read processor ID */
uint32_t vexpress_get_proc_id(void) {
    return mmio_read(VEXPRESS_SYSREG_BASE + SYSREG_PROC_ID0);
}

/* Read 100Hz counter (for coarse timing) */
uint32_t vexpress_get_100hz_counter(void) {
    return mmio_read(VEXPRESS_SYSREG_BASE + SYSREG_100HZ);
}

/* Read switch states */
uint32_t vexpress_get_switches(void) {
    return mmio_read(VEXPRESS_SYSREG_BASE + SYSREG_SW);
}

/* System reset */
void vexpress_system_reset(void) {
    mmio_write(VEXPRESS_SYSREG_BASE + SYSREG_RESETCTL, 0x100);
}

/* ============================================================
 * Network Driver Stubs
 * ============================================================ */

#include "../common/net.h"

/* VExpress-A15 has LAN9118 or SMSC911x Ethernet */
static mac_addr_t vexpress_mac = {{ 0x02, 0x00, 0x00, 0x12, 0x34, 0x56 }};

int bsp_net_init(void) {
    return 0;
}

int bsp_net_link_up(void) {
    return 1;
}

void bsp_net_get_mac(mac_addr_t *mac) {
    int i;
    for (i = 0; i < 6; i++) {
        mac->addr[i] = vexpress_mac.addr[i];
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
    /* Avoid 64-bit division on ARM32 - use 100Hz counter instead */
    uint32_t ticks_100hz = vexpress_get_100hz_counter();
    return ticks_100hz * 10;  /* Convert 100Hz ticks to ms */
}

/* ============================================================
 * Storage Driver Stubs
 * ============================================================ */

/* VExpress-A15 has MMCI/PL180 SD controller at 0x1C050000.
 * Full implementation would require PL180 driver.
 */

#include "../common/storage.h"

int bsp_storage_init(int device) {
    (void)device;
    return -1;
}

int bsp_storage_present(int device) {
    (void)device;
    return 0;
}

int bsp_storage_info(int device, storage_info_t *info) {
    (void)device;
    (void)info;
    return -1;
}

int bsp_storage_read(int device, uint64_t block, uint32_t count, uint8_t *buffer) {
    (void)device;
    (void)block;
    (void)count;
    (void)buffer;
    return -1;
}

int bsp_storage_write(int device, uint64_t block, uint32_t count, const uint8_t *buffer) {
    (void)device;
    (void)block;
    (void)count;
    (void)buffer;
    return -1;
}
