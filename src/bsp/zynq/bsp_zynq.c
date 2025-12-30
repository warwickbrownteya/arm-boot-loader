/* Xilinx Zynq UltraScale+ ZCU102 BSP Implementation */

#include <stdint.h>
#include "../common/bsp.h"
#include "bsp_zynq.h"

/* BSP Information */
static const bsp_info_t zynq_bsp_info = {
    .id          = PLATFORM_ZYNQ_ZCU102,
    .name        = "Xilinx ZCU102",
    .description = "Zynq UltraScale+ MPSoC Evaluation Kit",
    .uart_base   = ZYNQ_UART0_BASE,
    .timer_base  = ZYNQ_TTC0_BASE,
    .gpio_base   = ZYNQ_GPIO_BASE,
    .ram_base    = 0x00000000,
    .ram_size    = 0x80000000,  /* 2GB DDR */
    .cpu_freq_hz = 100000000    /* 100 MHz reference clock */
};

/* ============================================================
 * MMIO Helpers
 * ============================================================ */

static inline void mmio_write(uint64_t reg, uint32_t data) {
    __asm__ volatile ("dsb sy" ::: "memory");
    *(volatile uint32_t*)(uintptr_t)reg = data;
    __asm__ volatile ("dmb sy" ::: "memory");
}

static inline uint32_t mmio_read(uint64_t reg) {
    __asm__ volatile ("dmb sy" ::: "memory");
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
    return &zynq_bsp_info;
}

/* ============================================================
 * Timer frequency constant (100 MHz TTC clock)
 * ============================================================ */
static const uint32_t timer_freq = 100000000;

/* Helper to get elapsed ticks with 16-bit wraparound handling */
static uint64_t get_elapsed_ticks(uint64_t *last) {
    uint64_t now = bsp_timer_get_ticks();
    uint64_t elapsed = 0;

    if (now >= *last) {
        elapsed = now - *last;
    } else {
        /* Wraparound */
        elapsed = (0xFFFF - *last + now + 1);
    }
    *last = now;
    return elapsed;
}

/* ============================================================
 * Cadence UART Implementation
 * ============================================================ */

void bsp_uart_init(void) {
    uint64_t base = ZYNQ_UART0_BASE;

    /* Disable TX and RX */
    mmio_write(base + UART_CR, UART_CR_TXDIS | UART_CR_RXDIS);

    /* Reset TX and RX */
    mmio_write(base + UART_CR, UART_CR_TXRST | UART_CR_RXRST);

    /* Configure mode: 8N1, no parity */
    mmio_write(base + UART_MR,
        UART_MR_CHMODE_NORM |
        UART_MR_NBSTOP_1 |
        UART_MR_PAR_NONE |
        UART_MR_CHARLEN_8);

    /* Set baud rate for 115200
     * With 100MHz reference clock:
     * Baud = ref_clk / (CD * (BDIV + 1))
     * For 115200: CD = 62, BDIV = 6 gives ~114943
     */
    mmio_write(base + UART_BAUDGEN, 62);    /* CD */
    mmio_write(base + UART_BAUDDIV, 6);     /* BDIV */

    /* Set RX/TX FIFO trigger level */
    mmio_write(base + UART_RXWM, 1);
    mmio_write(base + UART_TXWM, 1);

    /* Disable all interrupts */
    mmio_write(base + UART_IDR, 0xFFFFFFFF);

    /* Enable TX and RX */
    mmio_write(base + UART_CR, UART_CR_TXEN | UART_CR_RXEN);
}

/* Timeout-aware UART putc */
bsp_err_t bsp_uart_putc_timeout(char c, uint32_t timeout_ms) {
    uint64_t base = ZYNQ_UART0_BASE;
    uint64_t timeout_ticks;
    uint64_t elapsed = 0;
    uint64_t last = bsp_timer_get_ticks();

    /* 100 MHz = 100 ticks per microsecond = 100,000 ticks per ms */
    if (timeout_ms == BSP_TIMEOUT_INFINITE) {
        timeout_ticks = UINT64_MAX;
    } else {
        timeout_ticks = (uint64_t)timeout_ms * 100000;
    }

    /* Wait until TX FIFO not full, with timeout */
    while (mmio_read(base + UART_SR) & UART_SR_TXFULL) {
        elapsed += get_elapsed_ticks(&last);
        if (elapsed >= timeout_ticks) {
            return BSP_ERR_TIMEOUT;
        }
    }

    /* Write character */
    mmio_write(base + UART_FIFO, (uint32_t)c);
    return BSP_OK;
}

/* Timeout-aware UART getc */
bsp_err_t bsp_uart_getc_timeout(char *c, uint32_t timeout_ms) {
    uint64_t base = ZYNQ_UART0_BASE;
    uint64_t timeout_ticks;
    uint64_t elapsed = 0;
    uint64_t last = bsp_timer_get_ticks();

    if (c == NULL) {
        return BSP_ERR_INVALID;
    }

    if (timeout_ms == BSP_TIMEOUT_INFINITE) {
        timeout_ticks = UINT64_MAX;
    } else {
        timeout_ticks = (uint64_t)timeout_ms * 100000;
    }

    /* Wait until RX FIFO not empty, with timeout */
    while (mmio_read(base + UART_SR) & UART_SR_RXEMPTY) {
        elapsed += get_elapsed_ticks(&last);
        if (elapsed >= timeout_ticks) {
            return BSP_ERR_TIMEOUT;
        }
    }

    *c = (char)(mmio_read(base + UART_FIFO) & 0xFF);
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
    uint64_t base = ZYNQ_UART0_BASE;
    return !(mmio_read(base + UART_SR) & UART_SR_RXEMPTY);
}

/* Blocking UART puts (backwards compatible) */
void bsp_uart_puts(const char *s) {
    bsp_uart_puts_timeout(s, BSP_TIMEOUT_INFINITE);
}

/* ============================================================
 * Triple Timer Counter (TTC) Implementation
 * ============================================================ */

static uint32_t timer_prescale = 0;

void bsp_timer_init(void) {
    uint64_t base = ZYNQ_TTC0_BASE;

    /* Disable counter */
    mmio_write(base + TTC_CNT_CTRL, TTC_CNT_CTRL_DIS);

    /* Set clock control: no prescaling, internal clock */
    mmio_write(base + TTC_CLK_CTRL, 0);

    /* Reset counter */
    mmio_write(base + TTC_CNT_CTRL, TTC_CNT_CTRL_RST);

    /* Enable counter in overflow mode (free-running) */
    mmio_write(base + TTC_CNT_CTRL, 0);

    timer_prescale = 1;  /* No prescaling */
}

uint64_t bsp_timer_get_ticks(void) {
    uint64_t base = ZYNQ_TTC0_BASE;
    return (uint64_t)mmio_read(base + TTC_CNT_VAL);
}

void bsp_timer_delay_us(uint32_t us) {
    /* With 100MHz clock, 1 tick = 10ns, so 100 ticks = 1us */
    uint64_t ticks_per_us = 100;
    uint64_t target = (uint64_t)us * ticks_per_us;
    uint64_t start = bsp_timer_get_ticks();

    /* Handle 16-bit counter wraparound for TTC */
    uint64_t elapsed = 0;
    uint64_t last = start;

    while (elapsed < target) {
        uint64_t now = bsp_timer_get_ticks();
        if (now >= last) {
            elapsed += (now - last);
        } else {
            /* Wraparound */
            elapsed += (0xFFFF - last + now + 1);
        }
        last = now;
    }
}

void bsp_timer_delay_ms(uint32_t ms) {
    bsp_timer_delay_us(ms * 1000);
}

uint32_t bsp_timer_get_freq(void) {
    return timer_freq;
}

/* ============================================================
 * GPIO Implementation
 * ============================================================ */

void bsp_gpio_init(void) {
    /* GPIO is memory-mapped and always available */
}

void bsp_gpio_set_function(uint8_t pin, uint8_t function) {
    uint64_t base = ZYNQ_GPIO_BASE;
    uint32_t bank = pin / 32;
    uint32_t bit = pin % 32;

    uint64_t dirm_reg = (bank == 0) ? (base + GPIO_DIRM_0) : (base + GPIO_DIRM_1);
    uint64_t oen_reg = (bank == 0) ? (base + GPIO_OEN_0) : (base + GPIO_OEN_1);

    uint32_t dirm = mmio_read(dirm_reg);
    uint32_t oen = mmio_read(oen_reg);

    if (function == 1) {  /* Output */
        dirm |= (1 << bit);
        oen |= (1 << bit);
    } else {  /* Input */
        dirm &= ~(1 << bit);
        oen &= ~(1 << bit);
    }

    mmio_write(dirm_reg, dirm);
    mmio_write(oen_reg, oen);
}

void bsp_gpio_set(uint8_t pin) {
    uint64_t base = ZYNQ_GPIO_BASE;
    uint32_t bank = pin / 32;
    uint32_t bit = pin % 32;

    uint64_t data_reg = (bank == 0) ? (base + GPIO_DATA_0) : (base + GPIO_DATA_1);

    uint32_t data = mmio_read(data_reg);
    data |= (1 << bit);
    mmio_write(data_reg, data);
}

void bsp_gpio_clear(uint8_t pin) {
    uint64_t base = ZYNQ_GPIO_BASE;
    uint32_t bank = pin / 32;
    uint32_t bit = pin % 32;

    uint64_t data_reg = (bank == 0) ? (base + GPIO_DATA_0) : (base + GPIO_DATA_1);

    uint32_t data = mmio_read(data_reg);
    data &= ~(1 << bit);
    mmio_write(data_reg, data);
}

/* ============================================================
 * Network Driver Stubs
 * ============================================================ */

#include "../common/net.h"

/* Zynq UltraScale+ has GEM (Gigabit Ethernet MAC) */
static mac_addr_t zynq_mac = {{ 0x00, 0x0A, 0x35, 0x12, 0x34, 0x56 }};

int bsp_net_init(void) {
    return 0;
}

int bsp_net_link_up(void) {
    return 1;
}

void bsp_net_get_mac(mac_addr_t *mac) {
    for (int i = 0; i < 6; i++) {
        mac->addr[i] = zynq_mac.addr[i];
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
 * Storage Driver Stubs
 * ============================================================ */

/* Zynq UltraScale+ has SD/eMMC via ARASAN SDHCI controller.
 * Full implementation would require SDHCI driver similar to raspi.
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
