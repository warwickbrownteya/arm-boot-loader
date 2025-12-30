/* Common BSP Interface Header
 * All platform BSPs must implement these functions
 * Supports both 32-bit (ARMv7) and 64-bit (AArch64) platforms
 */

#ifndef BSP_H
#define BSP_H

#include <stdint.h>
#include <stddef.h>  /* For NULL */

/* Architecture detection */
#if defined(__aarch64__) || defined(__LP64__)
    #define BSP_ARCH_64BIT 1
    typedef uint64_t bsp_addr_t;
#else
    #define BSP_ARCH_32BIT 1
    typedef uint32_t bsp_addr_t;
#endif

/* Platform identification */
typedef enum {
    PLATFORM_UNKNOWN = 0,
    PLATFORM_RASPI3,        /* AArch64 */
    PLATFORM_RASPI4,        /* AArch64 */
    PLATFORM_QEMU_VIRT,     /* AArch64 */
    PLATFORM_ZYNQ_ZCU102,   /* AArch64 */
    PLATFORM_VEXPRESS_A15,  /* ARMv7-A (32-bit) */
    PLATFORM_SBSA_REF,      /* AArch64 - Server class */
    PLATFORM_IMX8MP         /* AArch64 */
} platform_id_t;

/* BSP information structure - uses bsp_addr_t for portability */
typedef struct {
    platform_id_t   id;
    const char     *name;
    const char     *description;
    bsp_addr_t      uart_base;
    bsp_addr_t      timer_base;
    bsp_addr_t      gpio_base;
    bsp_addr_t      ram_base;
    bsp_addr_t      ram_size;
    uint32_t        cpu_freq_hz;
} bsp_info_t;

/* ============================================================
 * Error Codes
 * ============================================================ */

typedef enum {
    BSP_OK = 0,             /* Success */
    BSP_ERR_TIMEOUT = -1,   /* Operation timed out */
    BSP_ERR_BUSY = -2,      /* Resource busy */
    BSP_ERR_INVALID = -3,   /* Invalid parameter */
    BSP_ERR_NODEV = -4,     /* Device not available */
    BSP_ERR_IO = -5         /* I/O error */
} bsp_err_t;

/* Default timeout values (in milliseconds) */
#define BSP_TIMEOUT_INFINITE    0xFFFFFFFF
#define BSP_TIMEOUT_DEFAULT     1000    /* 1 second */
#define BSP_TIMEOUT_SHORT       100     /* 100 ms */

/* ============================================================
 * Required BSP functions - all platforms must implement
 * ============================================================ */

/* Initialize the BSP (called first) */
void bsp_init(void);

/* Get BSP information */
const bsp_info_t* bsp_get_info(void);

/* UART functions - blocking (backwards compatible) */
void bsp_uart_init(void);
void bsp_uart_putc(char c);
char bsp_uart_getc(void);
int  bsp_uart_tstc(void);  /* Test if char available */
void bsp_uart_puts(const char *s);

/* UART functions - with timeout (new, recommended)
 * timeout_ms: timeout in milliseconds, or BSP_TIMEOUT_INFINITE for blocking
 * Returns: BSP_OK on success, BSP_ERR_TIMEOUT on timeout, other errors as applicable
 */
bsp_err_t bsp_uart_putc_timeout(char c, uint32_t timeout_ms);
bsp_err_t bsp_uart_getc_timeout(char *c, uint32_t timeout_ms);
bsp_err_t bsp_uart_puts_timeout(const char *s, uint32_t timeout_ms);

/* Timer functions */
void     bsp_timer_init(void);
uint64_t bsp_timer_get_ticks(void);
uint32_t bsp_timer_get_freq(void);  /* Get timer frequency in Hz */
void     bsp_timer_delay_us(uint32_t us);
void     bsp_timer_delay_ms(uint32_t ms);

/* GPIO functions (optional - may be no-op on some platforms) */
void bsp_gpio_init(void);
void bsp_gpio_set_function(uint8_t pin, uint8_t function);
void bsp_gpio_set(uint8_t pin);
void bsp_gpio_clear(uint8_t pin);

/* Memory barrier functions - architecture independent */
#ifdef BSP_ARCH_64BIT
static inline void bsp_dmb(void) {
    __asm__ volatile ("dmb sy" ::: "memory");
}

static inline void bsp_dsb(void) {
    __asm__ volatile ("dsb sy" ::: "memory");
}

static inline void bsp_isb(void) {
    __asm__ volatile ("isb" ::: "memory");
}
#else /* BSP_ARCH_32BIT */
static inline void bsp_dmb(void) {
    __asm__ volatile ("dmb" ::: "memory");
}

static inline void bsp_dsb(void) {
    __asm__ volatile ("dsb" ::: "memory");
}

static inline void bsp_isb(void) {
    __asm__ volatile ("isb" ::: "memory");
}
#endif

/* MMIO access helpers - uses bsp_addr_t for portability */
static inline void bsp_mmio_write32(bsp_addr_t reg, uint32_t data) {
    bsp_dsb();
    *(volatile uint32_t*)(uintptr_t)reg = data;
    bsp_dmb();
}

static inline uint32_t bsp_mmio_read32(bsp_addr_t reg) {
    bsp_dmb();
    return *(volatile uint32_t*)(uintptr_t)reg;
}

#endif /* BSP_H */
