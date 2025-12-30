/* QEMU Virt Machine BSP Implementation */

#include <stdint.h>
#include "../common/bsp.h"
#include "bsp_virt.h"

/* BSP Information */
static const bsp_info_t virt_bsp_info = {
    .id          = PLATFORM_QEMU_VIRT,
    .name        = "QEMU Virt",
    .description = "QEMU ARM Virtual Machine",
    .uart_base   = VIRT_UART_BASE,
    .timer_base  = 0,  /* Uses system registers */
    .gpio_base   = VIRT_GPIO_BASE,
    .ram_base    = VIRT_RAM_BASE,
    .ram_size    = VIRT_RAM_SIZE,
    .cpu_freq_hz = 62500000  /* 62.5 MHz default */
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
    return &virt_bsp_info;
}

/* ============================================================
 * PL011 UART Implementation
 * ============================================================ */

void bsp_uart_init(void) {
    uint64_t base = VIRT_UART_BASE;

    /* Disable UART */
    mmio_write(base + PL011_CR, 0);

    /* Wait for any pending transmission */
    while (mmio_read(base + PL011_FR) & PL011_FR_BUSY);

    /* Clear all interrupt flags */
    mmio_write(base + PL011_ICR, 0x7FF);

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
    uint64_t base = VIRT_UART_BASE;
    uint64_t start = read_cntpct();
    uint64_t timeout_ticks;

    /* Calculate timeout in timer ticks */
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
    return BSP_OK;
}

/* Timeout-aware UART getc */
bsp_err_t bsp_uart_getc_timeout(char *c, uint32_t timeout_ms) {
    uint64_t base = VIRT_UART_BASE;
    uint64_t start = read_cntpct();
    uint64_t timeout_ticks;

    if (c == NULL) {
        return BSP_ERR_INVALID;
    }

    /* Calculate timeout in timer ticks */
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

    /* Read character */
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
    uint64_t base = VIRT_UART_BASE;
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

    uint64_t base = VIRT_GPIO_BASE;
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
    uint64_t addr = VIRT_GPIO_BASE + PL061_DATA + ((1 << pin) << 2);
    mmio_write(addr, 0xFF);
}

void bsp_gpio_clear(uint8_t pin) {
    if (pin > 7) return;

    uint64_t addr = VIRT_GPIO_BASE + PL061_DATA + ((1 << pin) << 2);
    mmio_write(addr, 0x00);
}

/* ============================================================
 * Network Driver Stubs
 * ============================================================ */

/* Note: QEMU virt machine can have virtio-net, but full implementation
 * requires virtio driver. These stubs allow compilation and testing
 * of the network stack protocol code.
 */

#include "../common/net.h"

static mac_addr_t virt_mac = {{ 0x52, 0x54, 0x00, 0x12, 0x34, 0x56 }};

int bsp_net_init(void) {
    /* In a full implementation, this would initialize virtio-net */
    return 0;  /* Return 0 for success to test protocol stack */
}

int bsp_net_link_up(void) {
    /* Report link as up for testing */
    return 1;
}

void bsp_net_get_mac(mac_addr_t *mac) {
    for (int i = 0; i < 6; i++) {
        mac->addr[i] = virt_mac.addr[i];
    }
}

int bsp_net_send(const uint8_t *data, size_t len) {
    (void)data;
    (void)len;
    /* Stub: would send via virtio-net */
    return 0;
}

int bsp_net_recv(uint8_t *data, size_t maxlen) {
    (void)data;
    (void)maxlen;
    /* Stub: no packets available */
    return 0;
}

uint32_t bsp_net_get_time_ms(void) {
    return (uint32_t)(read_cntpct() * 1000 / timer_freq);
}

/* ============================================================
 * Virtio-blk Storage Driver
 * ============================================================ */

#include "../common/storage.h"

/* Virtio MMIO base address range in QEMU virt (32 slots, 0x200 apart) */
#define VIRTIO_MMIO_START    0x0a000000
#define VIRTIO_MMIO_SIZE     0x200
#define VIRTIO_MMIO_SLOTS    32

/* Actual base address found during scan */
static uint64_t virtio_mmio_base = 0;

/* Virtio MMIO registers */
#define VIRTIO_MAGIC         0x000
#define VIRTIO_VERSION       0x004
#define VIRTIO_DEVICE_ID     0x008
#define VIRTIO_VENDOR_ID     0x00c
#define VIRTIO_DEV_FEATURES  0x010
#define VIRTIO_DEV_FEAT_SEL  0x014
#define VIRTIO_DRV_FEATURES  0x020
#define VIRTIO_DRV_FEAT_SEL  0x024
#define VIRTIO_QUEUE_SEL     0x030
#define VIRTIO_QUEUE_NUM_MAX 0x034
#define VIRTIO_QUEUE_NUM     0x038
#define VIRTIO_QUEUE_READY   0x044
#define VIRTIO_QUEUE_NOTIFY  0x050
#define VIRTIO_INT_STATUS    0x060
#define VIRTIO_INT_ACK       0x064
#define VIRTIO_STATUS        0x070
#define VIRTIO_QUEUE_DESC_LO 0x080
#define VIRTIO_QUEUE_DESC_HI 0x084
#define VIRTIO_QUEUE_AVAIL_LO 0x090
#define VIRTIO_QUEUE_AVAIL_HI 0x094
#define VIRTIO_QUEUE_USED_LO  0x0a0
#define VIRTIO_QUEUE_USED_HI  0x0a4
#define VIRTIO_CONFIG        0x100

/* Virtio status bits */
#define VIRTIO_STATUS_ACK         1
#define VIRTIO_STATUS_DRIVER      2
#define VIRTIO_STATUS_DRIVER_OK   4
#define VIRTIO_STATUS_FEATURES_OK 8
#define VIRTIO_STATUS_FAILED      128

/* Virtio device IDs */
#define VIRTIO_DEV_BLK   2

/* Virtio feature bits */
#define VIRTIO_F_VERSION_1  (1UL << 32)

/* Virtio blk request types */
#define VIRTIO_BLK_T_IN  0
#define VIRTIO_BLK_T_OUT 1

/* Virtio queue descriptor flags */
#define VIRTQ_DESC_F_NEXT     1
#define VIRTQ_DESC_F_WRITE    2

/* Queue size */
#define VIRTQ_SIZE  16

/* Virtio queue descriptor */
typedef struct {
    uint64_t addr;
    uint32_t len;
    uint16_t flags;
    uint16_t next;
} __attribute__((packed)) virtq_desc_t;

/* Virtio available ring */
typedef struct {
    uint16_t flags;
    uint16_t idx;
    uint16_t ring[VIRTQ_SIZE];
    uint16_t used_event;
} __attribute__((packed)) virtq_avail_t;

/* Virtio used ring element */
typedef struct {
    uint32_t id;
    uint32_t len;
} __attribute__((packed)) virtq_used_elem_t;

/* Virtio used ring */
typedef struct {
    uint16_t flags;
    uint16_t idx;
    virtq_used_elem_t ring[VIRTQ_SIZE];
    uint16_t avail_event;
} __attribute__((packed)) virtq_used_t;

/* Virtio block request header */
typedef struct {
    uint32_t type;
    uint32_t reserved;
    uint64_t sector;
} __attribute__((packed)) virtio_blk_req_t;

/* Virtio block config */
typedef struct {
    uint64_t capacity;
    uint32_t size_max;
    uint32_t seg_max;
    uint16_t cylinders;
    uint8_t  heads;
    uint8_t  sectors;
    uint32_t blk_size;
} __attribute__((packed)) virtio_blk_config_t;

/* Driver state */
static struct {
    int initialized;
    uint64_t capacity_blocks;
    uint32_t block_size;

    /* Queue structures (aligned) */
    virtq_desc_t  *desc;
    virtq_avail_t *avail;
    virtq_used_t  *used;
    uint16_t last_used_idx;

    /* Request structures */
    virtio_blk_req_t req;
    uint8_t status;
} virtio_blk;

/* Aligned memory for virtqueue (page aligned) */
static uint8_t virtq_mem[4096] __attribute__((aligned(4096)));
static uint8_t sector_buffer[512] __attribute__((aligned(16)));

static inline void virtio_write(uint32_t offset, uint32_t val) {
    mmio_write(virtio_mmio_base + offset, val);
}

static inline uint32_t virtio_read(uint32_t offset) {
    return mmio_read(virtio_mmio_base + offset);
}

/* Scan for virtio-blk device */
static int virtio_find_blk(void) {
    for (int slot = 0; slot < VIRTIO_MMIO_SLOTS; slot++) {
        uint64_t base = VIRTIO_MMIO_START + (slot * VIRTIO_MMIO_SIZE);
        uint32_t magic = mmio_read(base + VIRTIO_MAGIC);
        uint32_t dev_id = mmio_read(base + VIRTIO_DEVICE_ID);

        if (magic == 0x74726976 && dev_id == VIRTIO_DEV_BLK) {
            virtio_mmio_base = base;
            return 0;
        }
    }
    return -1;  /* Not found */
}

int bsp_storage_init(int device) {
    uint32_t status;
    virtio_blk_config_t *cfg;

    if (device != 0) return -1;
    if (virtio_blk.initialized) return 0;

    /* Scan for virtio-blk device */
    if (virtio_find_blk() != 0) {
        return -1;  /* No virtio-blk device found */
    }

    /* Reset device */
    virtio_write(VIRTIO_STATUS, 0);
    __asm__ volatile("dmb sy" ::: "memory");

    /* Acknowledge */
    status = VIRTIO_STATUS_ACK;
    virtio_write(VIRTIO_STATUS, status);

    /* Driver */
    status |= VIRTIO_STATUS_DRIVER;
    virtio_write(VIRTIO_STATUS, status);

    /* Read device features */
    virtio_write(VIRTIO_DEV_FEAT_SEL, 0);
    uint32_t features_lo = virtio_read(VIRTIO_DEV_FEATURES);
    virtio_write(VIRTIO_DEV_FEAT_SEL, 1);
    uint32_t features_hi = virtio_read(VIRTIO_DEV_FEATURES);

    /* Negotiate VIRTIO_F_VERSION_1 (bit 32, in high word) */
    virtio_write(VIRTIO_DRV_FEAT_SEL, 0);
    virtio_write(VIRTIO_DRV_FEATURES, 0);  /* No low features needed */
    virtio_write(VIRTIO_DRV_FEAT_SEL, 1);
    virtio_write(VIRTIO_DRV_FEATURES, features_hi & 1);  /* Accept VERSION_1 if offered */
    (void)features_lo;  /* Suppress unused warning */

    /* Features OK */
    status |= VIRTIO_STATUS_FEATURES_OK;
    virtio_write(VIRTIO_STATUS, status);

    /* Check features OK */
    if (!(virtio_read(VIRTIO_STATUS) & VIRTIO_STATUS_FEATURES_OK)) {
        virtio_write(VIRTIO_STATUS, VIRTIO_STATUS_FAILED);
        return -1;
    }

    /* Setup virtqueue */
    virtio_write(VIRTIO_QUEUE_SEL, 0);

    uint32_t max_q = virtio_read(VIRTIO_QUEUE_NUM_MAX);
    if (max_q == 0 || max_q < VIRTQ_SIZE) {
        virtio_write(VIRTIO_STATUS, VIRTIO_STATUS_FAILED);
        return -1;
    }

    virtio_write(VIRTIO_QUEUE_NUM, VIRTQ_SIZE);

    /* Setup queue memory */
    virtio_blk.desc = (virtq_desc_t *)virtq_mem;
    virtio_blk.avail = (virtq_avail_t *)(virtq_mem + VIRTQ_SIZE * sizeof(virtq_desc_t));
    virtio_blk.used = (virtq_used_t *)(virtq_mem + 2048);  /* Second half of page */
    virtio_blk.last_used_idx = 0;

    /* Clear queue memory */
    for (int i = 0; i < (int)sizeof(virtq_mem); i++) {
        virtq_mem[i] = 0;
    }

    /* Set queue addresses (modern MMIO) */
    uint64_t desc_addr = (uint64_t)(uintptr_t)virtio_blk.desc;
    uint64_t avail_addr = (uint64_t)(uintptr_t)virtio_blk.avail;
    uint64_t used_addr = (uint64_t)(uintptr_t)virtio_blk.used;

    virtio_write(VIRTIO_QUEUE_DESC_LO, (uint32_t)desc_addr);
    virtio_write(VIRTIO_QUEUE_DESC_HI, (uint32_t)(desc_addr >> 32));
    virtio_write(VIRTIO_QUEUE_AVAIL_LO, (uint32_t)avail_addr);
    virtio_write(VIRTIO_QUEUE_AVAIL_HI, (uint32_t)(avail_addr >> 32));
    virtio_write(VIRTIO_QUEUE_USED_LO, (uint32_t)used_addr);
    virtio_write(VIRTIO_QUEUE_USED_HI, (uint32_t)(used_addr >> 32));

    /* Enable queue */
    virtio_write(VIRTIO_QUEUE_READY, 1);

    /* Driver ready */
    status |= VIRTIO_STATUS_DRIVER_OK;
    virtio_write(VIRTIO_STATUS, status);

    /* Read device config */
    cfg = (virtio_blk_config_t *)(uintptr_t)(virtio_mmio_base + VIRTIO_CONFIG);
    virtio_blk.capacity_blocks = cfg->capacity;
    virtio_blk.block_size = cfg->blk_size;
    if (virtio_blk.block_size == 0) {
        virtio_blk.block_size = 512;
    }

    virtio_blk.initialized = 1;

    return 0;
}

int bsp_storage_present(int device) {
    if (device != 0) return 0;

    /* If already found, return true */
    if (virtio_mmio_base != 0) return 1;

    /* Try to find */
    return (virtio_find_blk() == 0);
}

int bsp_storage_info(int device, storage_info_t *info) {
    if (device != 0 || !virtio_blk.initialized) {
        return -1;
    }

    info->type = STORAGE_TYPE_SD;  /* Report as SD for compatibility */
    info->initialized = 1;
    info->block_size = virtio_blk.block_size;
    info->total_blocks = virtio_blk.capacity_blocks;
    info->capacity_mb = (uint32_t)(virtio_blk.capacity_blocks * virtio_blk.block_size / (1024 * 1024));

    /* Copy vendor/product info */
    const char *vendor = "QEMU";
    const char *product = "Virtio-blk";
    int i;
    for (i = 0; vendor[i] && i < 15; i++) info->vendor[i] = vendor[i];
    info->vendor[i] = '\0';
    for (i = 0; product[i] && i < 31; i++) info->product[i] = product[i];
    info->product[i] = '\0';
    info->serial[0] = '\0';

    return 0;
}

/* Read blocks using virtio */
int bsp_storage_read(int device, uint64_t block, uint32_t count, uint8_t *buffer) {
    if (device != 0 || !virtio_blk.initialized) {
        return -1;
    }

    if (block + count > virtio_blk.capacity_blocks) {
        return -1;
    }

    /* Read one block at a time */
    for (uint32_t i = 0; i < count; i++) {
        /* Setup request header */
        virtio_blk.req.type = VIRTIO_BLK_T_IN;
        virtio_blk.req.reserved = 0;
        virtio_blk.req.sector = block + i;
        virtio_blk.status = 0xFF;  /* Will be overwritten */

        /* Setup descriptor chain */
        /* Desc 0: Request header (device reads) */
        virtio_blk.desc[0].addr = (uint64_t)(uintptr_t)&virtio_blk.req;
        virtio_blk.desc[0].len = sizeof(virtio_blk_req_t);
        virtio_blk.desc[0].flags = VIRTQ_DESC_F_NEXT;
        virtio_blk.desc[0].next = 1;

        /* Desc 1: Data buffer (device writes) */
        virtio_blk.desc[1].addr = (uint64_t)(uintptr_t)sector_buffer;
        virtio_blk.desc[1].len = 512;
        virtio_blk.desc[1].flags = VIRTQ_DESC_F_WRITE | VIRTQ_DESC_F_NEXT;
        virtio_blk.desc[1].next = 2;

        /* Desc 2: Status byte (device writes) */
        virtio_blk.desc[2].addr = (uint64_t)(uintptr_t)&virtio_blk.status;
        virtio_blk.desc[2].len = 1;
        virtio_blk.desc[2].flags = VIRTQ_DESC_F_WRITE;
        virtio_blk.desc[2].next = 0;

        /* Memory barrier before updating avail ring */
        __asm__ volatile("dmb sy" ::: "memory");

        /* Add to available ring */
        uint16_t avail_idx = virtio_blk.avail->idx;
        virtio_blk.avail->ring[avail_idx % VIRTQ_SIZE] = 0;
        __asm__ volatile("dmb sy" ::: "memory");
        virtio_blk.avail->idx = avail_idx + 1;
        __asm__ volatile("dmb sy" ::: "memory");

        /* Notify device */
        virtio_write(VIRTIO_QUEUE_NOTIFY, 0);

        /* Wait for completion */
        uint32_t timeout = 1000000;
        while (virtio_blk.used->idx == virtio_blk.last_used_idx) {
            __asm__ volatile("dmb sy" ::: "memory");
            if (--timeout == 0) {
                return -1;  /* Timeout */
            }
        }

        virtio_blk.last_used_idx++;

        /* Check status */
        if (virtio_blk.status != 0) {
            return -1;
        }

        /* Copy data to output buffer */
        for (int j = 0; j < 512; j++) {
            buffer[i * 512 + j] = sector_buffer[j];
        }
    }

    return 0;
}

int bsp_storage_write(int device, uint64_t block, uint32_t count, const uint8_t *buffer) {
    if (device != 0 || !virtio_blk.initialized) {
        return -1;
    }

    if (block + count > virtio_blk.capacity_blocks) {
        return -1;
    }

    /* Write one block at a time */
    for (uint32_t i = 0; i < count; i++) {
        /* Copy data to sector buffer */
        for (int j = 0; j < 512; j++) {
            sector_buffer[j] = buffer[i * 512 + j];
        }

        /* Setup request header */
        virtio_blk.req.type = VIRTIO_BLK_T_OUT;
        virtio_blk.req.reserved = 0;
        virtio_blk.req.sector = block + i;
        virtio_blk.status = 0xFF;

        /* Setup descriptor chain */
        virtio_blk.desc[0].addr = (uint64_t)(uintptr_t)&virtio_blk.req;
        virtio_blk.desc[0].len = sizeof(virtio_blk_req_t);
        virtio_blk.desc[0].flags = VIRTQ_DESC_F_NEXT;
        virtio_blk.desc[0].next = 1;

        virtio_blk.desc[1].addr = (uint64_t)(uintptr_t)sector_buffer;
        virtio_blk.desc[1].len = 512;
        virtio_blk.desc[1].flags = VIRTQ_DESC_F_NEXT;  /* Device reads this */
        virtio_blk.desc[1].next = 2;

        virtio_blk.desc[2].addr = (uint64_t)(uintptr_t)&virtio_blk.status;
        virtio_blk.desc[2].len = 1;
        virtio_blk.desc[2].flags = VIRTQ_DESC_F_WRITE;
        virtio_blk.desc[2].next = 0;

        __asm__ volatile("dmb sy" ::: "memory");

        uint16_t avail_idx = virtio_blk.avail->idx;
        virtio_blk.avail->ring[avail_idx % VIRTQ_SIZE] = 0;
        __asm__ volatile("dmb sy" ::: "memory");
        virtio_blk.avail->idx = avail_idx + 1;
        __asm__ volatile("dmb sy" ::: "memory");

        virtio_write(VIRTIO_QUEUE_NOTIFY, 0);

        uint32_t timeout = 1000000;
        while (virtio_blk.used->idx == virtio_blk.last_used_idx) {
            __asm__ volatile("dmb sy" ::: "memory");
            if (--timeout == 0) {
                return -1;
            }
        }

        virtio_blk.last_used_idx++;

        if (virtio_blk.status != 0) {
            return -1;
        }
    }

    return 0;
}
