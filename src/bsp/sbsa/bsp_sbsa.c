/* ARM SBSA-Compatible Platform BSP Implementation
 *
 * Configured for addresses within 4GB to ensure reliable GOT operations.
 * Uses QEMU 'virt' machine peripheral addresses for testing.
 */

#include <stdint.h>
#include "../common/bsp.h"
#include "bsp_sbsa.h"

/* BSP Information - must be const for proper placement in .rodata */
static const bsp_info_t sbsa_bsp_info = {
    .id          = PLATFORM_SBSA_REF,
    .name        = "SBSA Compatible",
    .description = "Server (8GB max)",
    .uart_base   = 0x09000000,          /* PL011 UART */
    .timer_base  = 0,                   /* ARM Generic Timer via sysregs */
    .gpio_base   = 0x09030000,          /* PL061 GPIO */
    .ram_base    = 0x40000000,          /* 1GB base address */
    .ram_size    = 0x200000000,         /* 8GB max */
    .cpu_freq_hz = 1000000000
};

/* Timer frequency from CNTFRQ_EL0 */
static uint32_t timer_freq = 0;

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
 * ARM Generic Timer Helpers (needed by UART timeout)
 * ============================================================ */

/* Read counter frequency */
static inline uint32_t read_cntfrq(void) {
    uint32_t val;
    __asm__ volatile ("mrs %0, cntfrq_el0" : "=r"(val));
    return val;
}

/* Read physical counter */
static inline uint64_t read_cntpct(void) {
    uint64_t val;
    __asm__ volatile ("mrs %0, cntpct_el0" : "=r"(val));
    return val;
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
    return &sbsa_bsp_info;
}

/* ============================================================
 * PL011 UART Implementation
 * ============================================================ */

void bsp_uart_init(void) {
    uint64_t base = SBSA_UART_BASE;

    /* Disable UART */
    mmio_write(base + PL011_CR, 0);

    /* Wait for any pending transmission */
    while (mmio_read(base + PL011_FR) & PL011_FR_BUSY);

    /* Clear all interrupt flags */
    mmio_write(base + PL011_ICR, 0x7FF);

    /* Flush FIFOs by disabling them */
    mmio_write(base + PL011_LCR_H, 0);

    /* Set baud rate: 115200 @ 24MHz clock
     * Divisor = 24000000 / (16 * 115200) = 13.0208
     * IBRD = 13, FBRD = (0.0208 * 64 + 0.5) = 1
     */
    mmio_write(base + PL011_IBRD, 13);
    mmio_write(base + PL011_FBRD, 1);

    /* 8 bits, no parity, 1 stop bit, FIFO enabled */
    mmio_write(base + PL011_LCR_H, PL011_LCR_H_WLEN_8 | PL011_LCR_H_FEN);

    /* Disable all interrupts */
    mmio_write(base + PL011_IMSC, 0);

    /* Enable UART, TX, RX */
    mmio_write(base + PL011_CR, PL011_CR_UARTEN | PL011_CR_TXE | PL011_CR_RXE);
}

/* Timeout-aware UART putc */
bsp_err_t bsp_uart_putc_timeout(char c, uint32_t timeout_ms) {
    uint64_t base = SBSA_UART_BASE;
    uint64_t start = read_cntpct();
    uint64_t timeout_ticks;

    if (timeout_ms == BSP_TIMEOUT_INFINITE) {
        timeout_ticks = UINT64_MAX;
    } else {
        timeout_ticks = (uint64_t)timeout_ms * timer_freq / 1000;
    }

    /* Wait until TX FIFO not full, with timeout */
    while (mmio_read(base + PL011_FR) & PL011_FR_TXFF) {
        if ((read_cntpct() - start) >= timeout_ticks) {
            return BSP_ERR_TIMEOUT;
        }
    }

    /* Write character */
    mmio_write(base + PL011_DR, (uint32_t)c);

    /* Wait for character to be transmitted (TX FIFO empty) */
    while (!(mmio_read(base + PL011_FR) & PL011_FR_TXFE)) {
        if ((read_cntpct() - start) >= timeout_ticks) {
            return BSP_ERR_TIMEOUT;
        }
    }

    return BSP_OK;
}

/* Timeout-aware UART getc */
bsp_err_t bsp_uart_getc_timeout(char *c, uint32_t timeout_ms) {
    uint64_t base = SBSA_UART_BASE;
    uint64_t start = read_cntpct();
    uint64_t timeout_ticks;

    if (c == NULL) {
        return BSP_ERR_INVALID;
    }

    if (timeout_ms == BSP_TIMEOUT_INFINITE) {
        timeout_ticks = UINT64_MAX;
    } else {
        timeout_ticks = (uint64_t)timeout_ms * timer_freq / 1000;
    }

    /* Wait until RX FIFO not empty, with timeout */
    while (mmio_read(base + PL011_FR) & PL011_FR_RXFE) {
        if ((read_cntpct() - start) >= timeout_ticks) {
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
    uint64_t base = SBSA_UART_BASE;
    return !(mmio_read(base + PL011_FR) & PL011_FR_RXFE);
}

/* Blocking UART puts (backwards compatible) */
void bsp_uart_puts(const char *s) {
    bsp_uart_puts_timeout(s, BSP_TIMEOUT_INFINITE);
}

/* ============================================================
 * ARM Generic Timer Implementation
 * ============================================================ */

void bsp_timer_init(void) {
    /* Read timer frequency from system register */
    timer_freq = read_cntfrq();

    /* If frequency is 0 (not set), use a default */
    if (timer_freq == 0) {
        timer_freq = 62500000;  /* 62.5 MHz */
    }
}

uint64_t bsp_timer_get_ticks(void) {
    return read_cntpct();
}

uint32_t bsp_timer_get_freq(void) {
    return timer_freq;
}

void bsp_timer_delay_us(uint32_t us) {
    uint64_t start = read_cntpct();
    uint64_t target = (uint64_t)us * timer_freq / 1000000;

    while ((read_cntpct() - start) < target);
}

void bsp_timer_delay_ms(uint32_t ms) {
    bsp_timer_delay_us(ms * 1000);
}

/* ============================================================
 * PL061 GPIO Implementation
 * ============================================================ */

void bsp_gpio_init(void) {
    /* GPIO is memory-mapped and always available */
    /* No special initialization required */
}

void bsp_gpio_set_function(uint8_t pin, uint8_t function) {
    if (pin > 7) return;  /* PL061 has 8 GPIO pins */

    uint64_t base = SBSA_GPIO_BASE;
    uint32_t dir = mmio_read(base + PL061_DIR);

    if (function == 1) {  /* Output */
        dir |= (1 << pin);
    } else {  /* Input */
        dir &= ~(1 << pin);
    }

    mmio_write(base + PL061_DIR, dir);
}

void bsp_gpio_set(uint8_t pin) {
    if (pin > 7) return;

    /* PL061 uses address bits [9:2] as mask */
    uint64_t addr = SBSA_GPIO_BASE + PL061_DATA + ((1 << pin) << 2);
    mmio_write(addr, 0xFF);
}

void bsp_gpio_clear(uint8_t pin) {
    if (pin > 7) return;

    uint64_t addr = SBSA_GPIO_BASE + PL061_DATA + ((1 << pin) << 2);
    mmio_write(addr, 0x00);
}

/* ============================================================
 * SBSA-specific Functions
 * ============================================================ */

/* Read system identification */
uint32_t sbsa_get_system_id(void) {
    /* SBSA doesn't have a standard system ID register */
    /* Return a constant identifier */
    return 0x53425341;  /* "SBSA" in ASCII */
}

/* Read GIC version */
uint32_t sbsa_get_gic_version(void) {
    /* SBSA uses GICv3 */
    return 3;
}

/* Get PCIe ECAM base address */
uint64_t sbsa_get_pcie_ecam_base(void) {
    return SBSA_PCIE_ECAM_BASE;
}

/* Get SMMU base address */
uint64_t sbsa_get_smmu_base(void) {
    return SBSA_SMMU_BASE;
}

/* Additional accessors for struct fields */
uint64_t sbsa_get_ram_base(void) {
    return SBSA_RAM_BASE;
}

uint64_t sbsa_get_ram_size(void) {
    return SBSA_RAM_SIZE;
}

uint64_t sbsa_get_uart_base(void) {
    return SBSA_UART_BASE;
}

uint64_t sbsa_get_gpio_base(void) {
    return SBSA_GPIO_BASE;
}

/* ============================================================
 * Network Driver Stubs
 * ============================================================ */

#include "../common/net.h"

static mac_addr_t sbsa_mac = {{ 0x52, 0x54, 0x00, 0x12, 0x34, 0x57 }};

int bsp_net_init(void) {
    return 0;
}

int bsp_net_link_up(void) {
    return 1;
}

void bsp_net_get_mac(mac_addr_t *mac) {
    for (int i = 0; i < 6; i++) {
        mac->addr[i] = sbsa_mac.addr[i];
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
    return (uint32_t)(read_cntpct() * 1000 / timer_freq);
}

/* ============================================================
 * Storage Driver Stubs
 * ============================================================ */

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
