/*
 * SD Card Driver for Raspberry Pi 3/4
 * BCM2837/BCM2711 EMMC (Arasan SDHCI) Controller
 *
 * This driver implements the SD card protocol using the EMMC controller.
 * GPIO pins 48-53 must be configured for SD card access.
 *
 * References:
 * - BCM2835 ARM Peripherals (Section 5 - EMMC)
 * - SD Physical Layer Simplified Specification
 * - SDHCI Specification
 */

#include <stdint.h>
#include <stddef.h>
#include "sd.h"
#include "uart.h"
#include "timer.h"
#include "memory.h"
#include "gpio.h"

/* Debug output control - set to 0 for production */
#define SD_DEBUG 1

#if SD_DEBUG
#define sd_debug(msg) uart_puts(msg)
#define sd_debug_hex(prefix, val) do { \
    uart_puts(prefix); \
    uart_puthex(val); \
    uart_puts("\n"); \
} while(0)
#else
#define sd_debug(msg)
#define sd_debug_hex(prefix, val)
#endif

/* Peripheral base addresses */
#ifndef PERIPHERAL_BASE
#define PERIPHERAL_BASE 0x3F000000  /* Pi 3 */
#endif

/* EMMC (Arasan SDHCI) Controller Registers */
#define EMMC_BASE           (PERIPHERAL_BASE + 0x300000)

#define EMMC_ARG2           (*(volatile uint32_t*)(EMMC_BASE + 0x00))
#define EMMC_BLKSIZECNT     (*(volatile uint32_t*)(EMMC_BASE + 0x04))
#define EMMC_ARG1           (*(volatile uint32_t*)(EMMC_BASE + 0x08))
#define EMMC_CMDTM          (*(volatile uint32_t*)(EMMC_BASE + 0x0C))
#define EMMC_RESP0          (*(volatile uint32_t*)(EMMC_BASE + 0x10))
#define EMMC_RESP1          (*(volatile uint32_t*)(EMMC_BASE + 0x14))
#define EMMC_RESP2          (*(volatile uint32_t*)(EMMC_BASE + 0x18))
#define EMMC_RESP3          (*(volatile uint32_t*)(EMMC_BASE + 0x1C))
#define EMMC_DATA           (*(volatile uint32_t*)(EMMC_BASE + 0x20))
#define EMMC_STATUS         (*(volatile uint32_t*)(EMMC_BASE + 0x24))
#define EMMC_CONTROL0       (*(volatile uint32_t*)(EMMC_BASE + 0x28))
#define EMMC_CONTROL1       (*(volatile uint32_t*)(EMMC_BASE + 0x2C))
#define EMMC_INTERRUPT      (*(volatile uint32_t*)(EMMC_BASE + 0x30))
#define EMMC_IRPT_MASK      (*(volatile uint32_t*)(EMMC_BASE + 0x34))
#define EMMC_IRPT_EN        (*(volatile uint32_t*)(EMMC_BASE + 0x38))
#define EMMC_CONTROL2       (*(volatile uint32_t*)(EMMC_BASE + 0x3C))
#define EMMC_FORCE_IRPT     (*(volatile uint32_t*)(EMMC_BASE + 0x50))
#define EMMC_BOOT_TIMEOUT   (*(volatile uint32_t*)(EMMC_BASE + 0x70))
#define EMMC_DBG_SEL        (*(volatile uint32_t*)(EMMC_BASE + 0x74))
#define EMMC_EXRDFIFO_CFG   (*(volatile uint32_t*)(EMMC_BASE + 0x80))
#define EMMC_EXRDFIFO_EN    (*(volatile uint32_t*)(EMMC_BASE + 0x84))
#define EMMC_TUNE_STEP      (*(volatile uint32_t*)(EMMC_BASE + 0x88))
#define EMMC_TUNE_STEPS_STD (*(volatile uint32_t*)(EMMC_BASE + 0x8C))
#define EMMC_TUNE_STEPS_DDR (*(volatile uint32_t*)(EMMC_BASE + 0x90))
#define EMMC_SPI_INT_SPT    (*(volatile uint32_t*)(EMMC_BASE + 0xF0))
#define EMMC_SLOTISR_VER    (*(volatile uint32_t*)(EMMC_BASE + 0xFC))

/* GPIO registers for SD card pins */
#define GPIO_BASE           (PERIPHERAL_BASE + 0x200000)
#define GPIO_GPFSEL4        (*(volatile uint32_t*)(GPIO_BASE + 0x10))
#define GPIO_GPFSEL5        (*(volatile uint32_t*)(GPIO_BASE + 0x14))
#define GPIO_GPPUD          (*(volatile uint32_t*)(GPIO_BASE + 0x94))
#define GPIO_GPPUDCLK1      (*(volatile uint32_t*)(GPIO_BASE + 0x9C))

/* GPIO function select values */
#define GPIO_FUNC_INPUT     0
#define GPIO_FUNC_OUTPUT    1
#define GPIO_FUNC_ALT0      4
#define GPIO_FUNC_ALT3      7

/* CONTROL0 register bits */
#define C0_SPI_MODE_EN      0x00100000
#define C0_HCTL_HS_EN       0x00000004
#define C0_HCTL_DWITDH      0x00000002

/* CONTROL1 register bits */
#define C1_SRST_DATA        0x04000000
#define C1_SRST_CMD         0x02000000
#define C1_SRST_HC          0x01000000
#define C1_TOUNIT_MAX       0x000E0000
#define C1_TOUNIT_DIS       0x000F0000
#define C1_CLK_GENSEL       0x00000020
#define C1_CLK_EN           0x00000004
#define C1_CLK_STABLE       0x00000002
#define C1_CLK_INTLEN       0x00000001

/* STATUS register bits */
#define SR_DAT_LEVEL1       0x1E000000
#define SR_CMD_LEVEL        0x01000000
#define SR_DAT_LEVEL0       0x00F00000
#define SR_DAT3_LEVEL       0x00800000
#define SR_DAT_INHIBIT      0x00000002
#define SR_CMD_INHIBIT      0x00000001

/* INTERRUPT register bits */
#define INT_ACMD_ERR        0x01000000
#define INT_DEND_ERR        0x00400000
#define INT_DCRC_ERR        0x00200000
#define INT_DTO_ERR         0x00100000
#define INT_CBAD_ERR        0x00080000
#define INT_CEND_ERR        0x00040000
#define INT_CCRC_ERR        0x00020000
#define INT_CTO_ERR         0x00010000
#define INT_ERR             0x00008000
#define INT_ENDBOOT         0x00004000
#define INT_BOOTACK         0x00002000
#define INT_RETUNE          0x00001000
#define INT_CARD            0x00000100
#define INT_READ_RDY        0x00000020
#define INT_WRITE_RDY       0x00000010
#define INT_BLOCK_GAP       0x00000004
#define INT_DATA_DONE       0x00000002
#define INT_CMD_DONE        0x00000001

#define INT_ERROR_MASK      (INT_CTO_ERR | INT_CCRC_ERR | INT_CEND_ERR | \
                             INT_CBAD_ERR | INT_DTO_ERR | INT_DCRC_ERR | \
                             INT_DEND_ERR | INT_ACMD_ERR)

/* Command flags for CMDTM register */
#define CMD_TYPE_NORMAL     0x00000000
#define CMD_TYPE_SUSPEND    0x00400000
#define CMD_TYPE_RESUME     0x00800000
#define CMD_TYPE_ABORT      0x00C00000
#define CMD_ISDATA          0x00200000
#define CMD_IXCHK_EN        0x00100000
#define CMD_CRCCHK_EN       0x00080000
#define CMD_RSPNS_NO        0x00000000
#define CMD_RSPNS_136       0x00010000
#define CMD_RSPNS_48        0x00020000
#define CMD_RSPNS_48B       0x00030000
#define TM_MULTI_BLOCK      0x00000020
#define TM_DAT_DIR_HC       0x00000000
#define TM_DAT_DIR_CH       0x00000010
#define TM_AUTO_CMD12       0x00000004
#define TM_AUTO_CMD23       0x00000008
#define TM_BLKCNT_EN        0x00000002

/* SD Commands */
#define SD_GO_IDLE_STATE        0   /* CMD0 */
#define SD_ALL_SEND_CID         2   /* CMD2 */
#define SD_SEND_RELATIVE_ADDR   3   /* CMD3 */
#define SD_SET_DSR              4   /* CMD4 */
#define SD_IO_SET_OP_COND       5   /* CMD5 - SDIO */
#define SD_SWITCH_FUNC          6   /* CMD6 */
#define SD_SELECT_CARD          7   /* CMD7 */
#define SD_SEND_IF_COND         8   /* CMD8 */
#define SD_SEND_CSD             9   /* CMD9 */
#define SD_SEND_CID             10  /* CMD10 */
#define SD_VOLTAGE_SWITCH       11  /* CMD11 */
#define SD_STOP_TRANSMISSION    12  /* CMD12 */
#define SD_SEND_STATUS          13  /* CMD13 */
#define SD_GO_INACTIVE_STATE    15  /* CMD15 */
#define SD_SET_BLOCKLEN         16  /* CMD16 */
#define SD_READ_SINGLE_BLOCK    17  /* CMD17 */
#define SD_READ_MULTIPLE_BLOCK  18  /* CMD18 */
#define SD_SEND_TUNING_BLOCK    19  /* CMD19 */
#define SD_SET_BLOCK_COUNT      23  /* CMD23 */
#define SD_WRITE_SINGLE_BLOCK   24  /* CMD24 */
#define SD_WRITE_MULTIPLE_BLOCK 25  /* CMD25 */
#define SD_APP_CMD              55  /* CMD55 */
#define SD_GEN_CMD              56  /* CMD56 */

/* SD App Commands (must be preceded by CMD55) */
#define SD_SET_BUS_WIDTH        6   /* ACMD6 */
#define SD_SD_STATUS            13  /* ACMD13 */
#define SD_SEND_NUM_WR_BLKS     22  /* ACMD22 */
#define SD_SET_WR_BLK_ERASE_CNT 23  /* ACMD23 */
#define SD_SD_SEND_OP_COND      41  /* ACMD41 */
#define SD_SET_CLR_CARD_DETECT  42  /* ACMD42 */
#define SD_SEND_SCR             51  /* ACMD51 */

/* Response types */
#define SD_RSP_NONE     0
#define SD_RSP_R1       1
#define SD_RSP_R1B      2
#define SD_RSP_R2       3
#define SD_RSP_R3       4
#define SD_RSP_R6       5
#define SD_RSP_R7       6

/* OCR register bits */
#define OCR_BUSY        0x80000000
#define OCR_HCS         0x40000000  /* High Capacity Support */
#define OCR_XPC         0x10000000  /* SDXC power control */
#define OCR_S18A        0x01000000  /* 1.8V switching accepted */
#define OCR_VOLTAGE     0x00FF8000  /* Voltage window */

/* SD Card state - volatile to prevent optimization issues */
static volatile struct {
    uint32_t initialized;
    uint32_t type;          /* 1=SDv1, 2=SDv2, 3=SDHC */
    uint32_t high_capacity; /* SDHC/SDXC flag */
    uint32_t rca;           /* Relative Card Address */
    uint32_t ocr;           /* OCR register value */
    uint32_t scr[2];        /* SCR register */
    uint32_t blocks;        /* Total blocks */
    uint32_t block_size;    /* Block size (usually 512) */
} sd_card;

/* Sector buffer for reads */
static uint8_t sector_buffer[512] __attribute__((aligned(16)));

/* Forward declarations */
static int sd_send_command(uint32_t cmd, uint32_t arg);
static int sd_send_app_command(uint32_t cmd, uint32_t arg);
static void sd_set_clock(uint32_t freq);

/*
 * Helper: print hex value to UART
 */
static void uart_puthex(uint32_t val) {
    static const char hex[] = "0123456789ABCDEF";
    char buf[11];
    buf[0] = '0';
    buf[1] = 'x';
    for (int i = 0; i < 8; i++) {
        buf[2 + i] = hex[(val >> (28 - i * 4)) & 0xF];
    }
    buf[10] = '\0';
    uart_puts(buf);
}

/*
 * Configure GPIO pins 48-53 for SD card (ALT0 function)
 * Also configure pull-ups for data lines
 */
static void sd_gpio_init(void) {
    /* GPIO 48-53 are in GPFSEL4 and GPFSEL5 */
    /* GPFSEL4 controls GPIO 40-49, GPFSEL5 controls GPIO 50-53 */

    /* Set GPIO 48-49 to ALT0 (bits 24-29 of GPFSEL4) */
    uint32_t sel4 = GPIO_GPFSEL4;
    sel4 &= ~(7 << 24);  /* Clear GPIO 48 */
    sel4 &= ~(7 << 27);  /* Clear GPIO 49 */
    sel4 |= (GPIO_FUNC_ALT0 << 24);  /* GPIO 48 = ALT0 (SD CLK) */
    sel4 |= (GPIO_FUNC_ALT0 << 27);  /* GPIO 49 = ALT0 (SD CMD) */
    GPIO_GPFSEL4 = sel4;

    /* Set GPIO 50-53 to ALT0 (bits 0-11 of GPFSEL5) */
    uint32_t sel5 = GPIO_GPFSEL5;
    sel5 &= ~(7 << 0);   /* Clear GPIO 50 */
    sel5 &= ~(7 << 3);   /* Clear GPIO 51 */
    sel5 &= ~(7 << 6);   /* Clear GPIO 52 */
    sel5 &= ~(7 << 9);   /* Clear GPIO 53 */
    sel5 |= (GPIO_FUNC_ALT0 << 0);   /* GPIO 50 = ALT0 (SD D0) */
    sel5 |= (GPIO_FUNC_ALT0 << 3);   /* GPIO 51 = ALT0 (SD D1) */
    sel5 |= (GPIO_FUNC_ALT0 << 6);   /* GPIO 52 = ALT0 (SD D2) */
    sel5 |= (GPIO_FUNC_ALT0 << 9);   /* GPIO 53 = ALT0 (SD D3) */
    GPIO_GPFSEL5 = sel5;

    /* Enable pull-ups on data lines (GPIO 50-53) and CMD (GPIO 49) */
    /* Pull-up/pull-down sequence per BCM2835 datasheet */
    GPIO_GPPUD = 2;  /* Enable pull-up */
    timer_delay_us(150);

    /* Clock the control signal into GPIO 49-53 */
    GPIO_GPPUDCLK1 = (1 << (49 - 32)) | (1 << (50 - 32)) |
                     (1 << (51 - 32)) | (1 << (52 - 32)) | (1 << (53 - 32));
    timer_delay_us(150);

    GPIO_GPPUD = 0;
    GPIO_GPPUDCLK1 = 0;

    sd_debug("  SD: GPIO configured\n");
}

/*
 * Reset the EMMC controller
 */
static int sd_reset_host(void) {
    uint32_t timeout;

    sd_debug("  SD: Resetting host controller...\n");

    /* Check if EMMC is present by reading version register */
    uint32_t ver_check = EMMC_SLOTISR_VER;

    /* QEMU raspi3b returns 0 for unimplemented peripherals */
    if (ver_check == 0xFFFFFFFF || ver_check == 0x00000000) {
        sd_debug("  SD: EMMC controller not found\n");
        return -1;
    }

    /* Reset the complete host circuit */
    EMMC_CONTROL0 = 0;
    EMMC_CONTROL1 = C1_SRST_HC;

    /* Wait for reset to complete */
    timeout = 10000;
    while ((EMMC_CONTROL1 & C1_SRST_HC) && timeout--) {
        timer_delay_us(10);
    }

    if (timeout == 0) {
        sd_debug("  SD: Host reset timeout\n");
        return -1;
    }

    /* Check host version */
    uint32_t ver = EMMC_SLOTISR_VER;
    sd_debug_hex("  SD: Host version: ", ver);

    /* Set data timeout */
    EMMC_CONTROL1 |= C1_TOUNIT_MAX;

    /* Enable internal clock */
    EMMC_CONTROL1 |= C1_CLK_INTLEN;

    /* Wait for clock to stabilize */
    timeout = 10000;
    while (!(EMMC_CONTROL1 & C1_CLK_STABLE) && timeout--) {
        timer_delay_us(10);
    }

    if (timeout == 0) {
        sd_debug("  SD: Clock stabilize timeout\n");
        return -1;
    }

    sd_debug("  SD: Host reset complete\n");
    return 0;
}

/*
 * Set SD clock frequency
 * freq: target frequency in Hz (400000 for init, 25000000 for normal)
 */
static void sd_set_clock(uint32_t freq) {
    uint32_t divider;
    uint32_t timeout;

    sd_debug_hex("  SD: Setting clock to ", freq);

    /* Disable clock */
    EMMC_CONTROL1 &= ~C1_CLK_EN;
    timer_delay_ms(2);

    /* Calculate divider
     * Base clock is 41.666667 MHz on Pi 3 (from VPU)
     * For 400 kHz: divider = 41666667 / 400000 = 104 -> use 128
     * For 25 MHz: divider = 41666667 / 25000000 = 1.67 -> use 2
     */
    uint32_t base_clock = 41666667;

    if (freq >= base_clock) {
        divider = 0;  /* Use base clock */
    } else {
        divider = base_clock / freq;
        if (divider > 0x3FF) divider = 0x3FF;  /* Max 10-bit divider */
    }

    /* BCM2835 uses different divider encoding */
    /* Upper 8 bits go to bits 15:8, lower 2 bits go to bits 7:6 */
    uint32_t div_hi = (divider >> 2) & 0xFF;
    uint32_t div_lo = divider & 0x03;

    uint32_t ctrl1 = EMMC_CONTROL1;
    ctrl1 &= ~0x0000FFE0;  /* Clear clock divider bits */
    ctrl1 |= (div_hi << 8) | (div_lo << 6);
    ctrl1 |= C1_CLK_INTLEN;  /* Enable internal clock */
    EMMC_CONTROL1 = ctrl1;

    /* Wait for clock stable */
    timeout = 10000;
    while (!(EMMC_CONTROL1 & C1_CLK_STABLE) && timeout--) {
        timer_delay_us(10);
    }

    /* Enable clock to card */
    EMMC_CONTROL1 |= C1_CLK_EN;
    timer_delay_ms(2);

    sd_debug("  SD: Clock configured\n");
}

/*
 * Wait for command/data lines to be free
 */
static int sd_wait_for_cmd(void) {
    uint32_t timeout = 100000;

    while ((EMMC_STATUS & SR_CMD_INHIBIT) && timeout--) {
        timer_delay_us(1);
    }

    if (timeout == 0) {
        sd_debug("  SD: Wait for CMD timeout\n");
        return -1;
    }

    return 0;
}

static int sd_wait_for_data(void) {
    uint32_t timeout = 500000;

    while ((EMMC_STATUS & SR_DAT_INHIBIT) && timeout--) {
        timer_delay_us(1);
    }

    if (timeout == 0) {
        sd_debug("  SD: Wait for DATA timeout\n");
        return -1;
    }

    return 0;
}

/*
 * Build command register value from command index and response type
 */
static uint32_t sd_build_cmd(uint32_t cmd_idx, uint32_t rsp_type, int is_data) {
    uint32_t cmd = (cmd_idx & 0x3F) << 24;

    switch (rsp_type) {
        case SD_RSP_NONE:
            cmd |= CMD_RSPNS_NO;
            break;
        case SD_RSP_R1:
        case SD_RSP_R6:
        case SD_RSP_R7:
            cmd |= CMD_RSPNS_48 | CMD_CRCCHK_EN | CMD_IXCHK_EN;
            break;
        case SD_RSP_R1B:
            cmd |= CMD_RSPNS_48B | CMD_CRCCHK_EN | CMD_IXCHK_EN;
            break;
        case SD_RSP_R2:
            cmd |= CMD_RSPNS_136 | CMD_CRCCHK_EN;
            break;
        case SD_RSP_R3:
            cmd |= CMD_RSPNS_48;  /* No CRC check for R3 */
            break;
    }

    if (is_data) {
        cmd |= CMD_ISDATA;
    }

    return cmd;
}

/*
 * Send a command to the SD card
 */
static int sd_send_command(uint32_t cmd_idx, uint32_t arg) {
    uint32_t cmd;
    uint32_t rsp_type;
    uint32_t timeout;
    uint32_t irq;

    /* Determine response type based on command */
    switch (cmd_idx) {
        case SD_GO_IDLE_STATE:
            rsp_type = SD_RSP_NONE;
            break;
        case SD_ALL_SEND_CID:
        case SD_SEND_CSD:
        case SD_SEND_CID:
            rsp_type = SD_RSP_R2;
            break;
        case SD_SEND_RELATIVE_ADDR:
            rsp_type = SD_RSP_R6;
            break;
        case SD_SELECT_CARD:
        case SD_STOP_TRANSMISSION:
            rsp_type = SD_RSP_R1B;
            break;
        case SD_SEND_IF_COND:
            rsp_type = SD_RSP_R7;
            break;
        case SD_SD_SEND_OP_COND:  /* ACMD41 */
            rsp_type = SD_RSP_R3;
            break;
        default:
            rsp_type = SD_RSP_R1;
            break;
    }

    /* Wait for command line free */
    if (sd_wait_for_cmd() != 0) {
        return -1;
    }

    /* Clear pending interrupts */
    EMMC_INTERRUPT = 0xFFFFFFFF;

    /* Build and send command */
    cmd = sd_build_cmd(cmd_idx, rsp_type, 0);
    EMMC_ARG1 = arg;
    EMMC_CMDTM = cmd;

    /* Wait for command complete or error */
    timeout = 100000;
    do {
        irq = EMMC_INTERRUPT;
        if (irq & INT_ERROR_MASK) {
            /* Clear error and return failure */
            EMMC_INTERRUPT = irq;
            sd_debug_hex("  SD: CMD error: ", irq);
            return -1;
        }
        timer_delay_us(1);
    } while (!(irq & INT_CMD_DONE) && timeout--);

    if (timeout == 0) {
        sd_debug("  SD: CMD timeout\n");
        return -1;
    }

    /* Clear command complete */
    EMMC_INTERRUPT = INT_CMD_DONE;

    return 0;
}

/*
 * Send an application-specific command (ACMD)
 * These must be preceded by CMD55
 */
static int sd_send_app_command(uint32_t cmd_idx, uint32_t arg) {
    /* Send CMD55 first */
    if (sd_send_command(SD_APP_CMD, sd_card.rca << 16) != 0) {
        sd_debug("  SD: CMD55 failed\n");
        return -1;
    }

    /* Then send the ACMD */
    return sd_send_command(cmd_idx, arg);
}

/*
 * Initialize the SD card
 */
int sd_init(void) {
    uint32_t resp;
    uint32_t timeout;
    int retries;

    sd_debug("SD: Initializing...\n");
    timer_delay_ms(2);  /* Allow UART to flush before peripheral access */

    /* Clear card state */
    sd_card.initialized = 0;
    sd_card.type = 0;
    sd_card.high_capacity = 0;
    sd_card.rca = 0;
    sd_card.ocr = 0;
    sd_card.blocks = 0;
    sd_card.block_size = 512;

    /* Step 1: Configure GPIO for SD card */
    sd_gpio_init();

    /* Step 2: Reset host controller */
    if (sd_reset_host() != 0) {
        sd_debug("SD: Host reset failed\n");
        return -1;
    }

    /* Step 3: Set initial clock (400 kHz for card identification) */
    sd_set_clock(400000);

    /* Step 4: Enable all interrupts for debugging */
    EMMC_IRPT_MASK = 0xFFFFFFFF;
    EMMC_IRPT_EN = 0xFFFFFFFF;

    /* Give card time to power up */
    timer_delay_ms(100);

    /* Step 5: CMD0 - GO_IDLE_STATE */
    sd_debug("SD: Sending CMD0 (GO_IDLE)...\n");
    retries = 3;
    while (retries--) {
        if (sd_send_command(SD_GO_IDLE_STATE, 0) == 0) {
            break;
        }
        timer_delay_ms(10);
    }
    if (retries < 0) {
        sd_debug("SD: CMD0 failed after retries\n");
        return -1;
    }
    sd_debug("SD: CMD0 OK\n");

    /* Step 6: CMD8 - SEND_IF_COND (check voltage) */
    sd_debug("SD: Sending CMD8 (IF_COND)...\n");
    /* Arg: voltage (0x1 = 2.7-3.6V) | check pattern (0xAA) */
    if (sd_send_command(SD_SEND_IF_COND, 0x000001AA) == 0) {
        resp = EMMC_RESP0;
        sd_debug_hex("SD: CMD8 response: ", resp);

        if ((resp & 0xFFF) == 0x1AA) {
            sd_card.type = 2;  /* SD v2.0 or later */
            sd_debug("SD: SD v2.0 card detected\n");
        } else {
            sd_debug("SD: Invalid CMD8 response\n");
            return -1;
        }
    } else {
        /* No response to CMD8 = SD v1.x or MMC */
        sd_card.type = 1;
        sd_debug("SD: SD v1.x card detected\n");
    }

    /* Step 7: ACMD41 - SD_SEND_OP_COND (initialize and get OCR) */
    sd_debug("SD: Sending ACMD41 (OP_COND)...\n");
    /* For SDHC: set HCS bit (0x40000000) and voltage window */
    uint32_t acmd41_arg = OCR_VOLTAGE;
    if (sd_card.type == 2) {
        acmd41_arg |= OCR_HCS;  /* Request SDHC if v2 card */
    }

    timeout = 100;  /* Up to 1 second (10ms * 100) */
    while (timeout--) {
        if (sd_send_app_command(SD_SD_SEND_OP_COND, acmd41_arg) != 0) {
            sd_debug("SD: ACMD41 send failed\n");
            timer_delay_ms(10);
            continue;
        }

        resp = EMMC_RESP0;
        if (resp & OCR_BUSY) {
            /* Card ready */
            sd_card.ocr = resp;
            sd_debug_hex("SD: OCR: ", resp);

            if (resp & OCR_HCS) {
                sd_card.high_capacity = 1;
                sd_debug("SD: SDHC/SDXC card\n");
            } else {
                sd_card.high_capacity = 0;
                sd_debug("SD: Standard capacity card\n");
            }
            break;
        }
        timer_delay_ms(10);
    }

    if (timeout == 0) {
        sd_debug("SD: ACMD41 timeout - card not ready\n");
        return -1;
    }
    sd_debug("SD: ACMD41 OK - card ready\n");

    /* Step 8: CMD2 - ALL_SEND_CID (get card identification) */
    sd_debug("SD: Sending CMD2 (ALL_SEND_CID)...\n");
    if (sd_send_command(SD_ALL_SEND_CID, 0) != 0) {
        sd_debug("SD: CMD2 failed\n");
        return -1;
    }
    sd_debug_hex("SD: CID[0]: ", EMMC_RESP0);
    sd_debug("SD: CMD2 OK\n");

    /* Step 9: CMD3 - SEND_RELATIVE_ADDR (get RCA) */
    sd_debug("SD: Sending CMD3 (SEND_RCA)...\n");
    if (sd_send_command(SD_SEND_RELATIVE_ADDR, 0) != 0) {
        sd_debug("SD: CMD3 failed\n");
        return -1;
    }
    resp = EMMC_RESP0;
    sd_card.rca = (resp >> 16) & 0xFFFF;
    sd_debug_hex("SD: RCA: ", sd_card.rca);
    sd_debug("SD: CMD3 OK\n");

    /* Step 10: Increase clock for data transfer (25 MHz) */
    sd_set_clock(25000000);

    /* Step 11: CMD7 - SELECT_CARD (put card in transfer state) */
    sd_debug("SD: Sending CMD7 (SELECT_CARD)...\n");
    if (sd_send_command(SD_SELECT_CARD, sd_card.rca << 16) != 0) {
        sd_debug("SD: CMD7 failed\n");
        return -1;
    }
    sd_debug("SD: CMD7 OK - card selected\n");

    /* Step 12: Set block size to 512 bytes */
    EMMC_BLKSIZECNT = 0x00000200;

    /* Optional: Set 4-bit bus width with ACMD6 */
    sd_debug("SD: Setting 4-bit bus width...\n");
    if (sd_send_app_command(SD_SET_BUS_WIDTH, 2) == 0) {
        EMMC_CONTROL0 |= C0_HCTL_DWITDH;  /* Enable 4-bit mode in host */
        sd_debug("SD: 4-bit mode enabled\n");
    } else {
        sd_debug("SD: 4-bit mode failed, using 1-bit\n");
    }

    sd_card.initialized = 1;
    sd_debug("SD: Initialization complete!\n");

    return 0;
}

/*
 * Read a single 512-byte sector from the SD card
 */
int sd_read_sector(uint32_t sector, uint8_t *buffer) {
    uint32_t cmd;
    uint32_t timeout;
    uint32_t irq;
    uint32_t *buf32;

    if (!sd_card.initialized) {
        sd_debug("SD: Not initialized\n");
        return -1;
    }

    if (buffer == NULL) {
        return -1;
    }

    /* For standard capacity cards, address is in bytes */
    /* For high capacity cards, address is in blocks */
    uint32_t addr = sd_card.high_capacity ? sector : (sector * 512);

    /* Wait for data line free */
    if (sd_wait_for_data() != 0) {
        sd_debug("SD: Data line busy\n");
        return -1;
    }

    /* Set block size and count */
    EMMC_BLKSIZECNT = (1 << 16) | 512;  /* 1 block of 512 bytes */

    /* Clear interrupts */
    EMMC_INTERRUPT = 0xFFFFFFFF;

    /* Send CMD17 - READ_SINGLE_BLOCK */
    cmd = sd_build_cmd(SD_READ_SINGLE_BLOCK, SD_RSP_R1, 1);
    cmd |= TM_DAT_DIR_CH;  /* Data from card to host */

    EMMC_ARG1 = addr;
    EMMC_CMDTM = cmd;

    /* Wait for command complete */
    timeout = 100000;
    do {
        irq = EMMC_INTERRUPT;
        if (irq & INT_ERROR_MASK) {
            EMMC_INTERRUPT = irq;
            sd_debug_hex("SD: Read CMD error: ", irq);
            return -1;
        }
        timer_delay_us(1);
    } while (!(irq & INT_CMD_DONE) && timeout--);

    if (timeout == 0) {
        sd_debug("SD: Read CMD timeout\n");
        return -1;
    }
    EMMC_INTERRUPT = INT_CMD_DONE;

    /* Wait for data ready */
    timeout = 500000;
    do {
        irq = EMMC_INTERRUPT;
        if (irq & INT_ERROR_MASK) {
            EMMC_INTERRUPT = irq;
            sd_debug_hex("SD: Read data error: ", irq);
            return -1;
        }
        timer_delay_us(1);
    } while (!(irq & INT_READ_RDY) && timeout--);

    if (timeout == 0) {
        sd_debug("SD: Read data timeout\n");
        return -1;
    }

    /* Read 512 bytes (128 x 32-bit words) */
    buf32 = (uint32_t *)buffer;
    for (int i = 0; i < 128; i++) {
        buf32[i] = EMMC_DATA;
    }

    /* Wait for transfer complete */
    timeout = 100000;
    do {
        irq = EMMC_INTERRUPT;
        timer_delay_us(1);
    } while (!(irq & INT_DATA_DONE) && timeout--);

    /* Clear interrupts */
    EMMC_INTERRUPT = 0xFFFFFFFF;

    return 0;
}

/*
 * Read multiple sectors
 */
int sd_read_sectors(uint32_t start_sector, uint32_t count, uint8_t *buffer) {
    for (uint32_t i = 0; i < count; i++) {
        if (sd_read_sector(start_sector + i, buffer + (i * 512)) != 0) {
            return -1;
        }
    }
    return 0;
}

/*
 * Check if SD card is initialized
 */
int sd_is_initialized(void) {
    return sd_card.initialized;
}

/* ============================================================
 * FAT32 Filesystem Implementation
 * ============================================================ */

static struct {
    uint8_t  initialized;
    uint32_t fat_begin_sector;
    uint32_t cluster_begin_sector;
    uint32_t sectors_per_cluster;
    uint32_t root_dir_cluster;
    uint32_t sectors_per_fat;
    uint32_t total_clusters;
} fat_state;

/*
 * Initialize FAT32 filesystem
 */
int fat_init(void) {
    uint8_t boot_sector[512];

    if (!sd_card.initialized) {
        sd_debug("FAT: SD not initialized\n");
        return -1;
    }

    sd_debug("FAT: Reading boot sector...\n");

    /* Read MBR/boot sector */
    if (sd_read_sector(0, boot_sector) != 0) {
        sd_debug("FAT: Failed to read boot sector\n");
        return -1;
    }

    /* Check for MBR signature */
    if (boot_sector[510] != 0x55 || boot_sector[511] != 0xAA) {
        sd_debug("FAT: Invalid boot signature\n");
        return -1;
    }

    /* Check if this is MBR (partition table) or VBR (volume boot record) */
    uint32_t partition_lba = 0;

    /* Check for FAT signature at expected location */
    if (boot_sector[0] == 0xEB || boot_sector[0] == 0xE9) {
        /* Likely a VBR (no partition table) */
        sd_debug("FAT: No partition table, using sector 0\n");
    } else {
        /* Check partition table entry 1 at offset 446 */
        uint8_t part_type = boot_sector[446 + 4];
        if (part_type == 0x0B || part_type == 0x0C) {
            /* FAT32 partition */
            partition_lba = boot_sector[446 + 8] |
                           (boot_sector[446 + 9] << 8) |
                           (boot_sector[446 + 10] << 16) |
                           (boot_sector[446 + 11] << 24);
            sd_debug_hex("FAT: Partition at LBA: ", partition_lba);

            /* Read the actual VBR */
            if (sd_read_sector(partition_lba, boot_sector) != 0) {
                sd_debug("FAT: Failed to read VBR\n");
                return -1;
            }
        }
    }

    /* Parse FAT32 BPB (BIOS Parameter Block) */
    fat_boot_sector_t *bpb = (fat_boot_sector_t *)boot_sector;

    /* Validate */
    if (bpb->bytes_per_sector != 512) {
        sd_debug("FAT: Invalid bytes per sector\n");
        return -1;
    }

    fat_state.sectors_per_cluster = bpb->sectors_per_cluster;
    fat_state.fat_begin_sector = partition_lba + bpb->reserved_sectors;
    fat_state.sectors_per_fat = bpb->sectors_per_fat_32;
    fat_state.cluster_begin_sector = fat_state.fat_begin_sector +
                                     (bpb->num_fats * bpb->sectors_per_fat_32);
    fat_state.root_dir_cluster = bpb->root_cluster;

    sd_debug_hex("FAT: Sectors per cluster: ", fat_state.sectors_per_cluster);
    sd_debug_hex("FAT: FAT begins at sector: ", fat_state.fat_begin_sector);
    sd_debug_hex("FAT: Clusters begin at sector: ", fat_state.cluster_begin_sector);
    sd_debug_hex("FAT: Root dir cluster: ", fat_state.root_dir_cluster);

    fat_state.initialized = 1;
    sd_debug("FAT: Filesystem initialized\n");

    return 0;
}

/*
 * Convert cluster number to first sector number
 */
static uint32_t cluster_to_sector(uint32_t cluster) {
    return fat_state.cluster_begin_sector +
           ((cluster - 2) * fat_state.sectors_per_cluster);
}

/*
 * Get next cluster from FAT chain
 */
static uint32_t fat_get_next_cluster(uint32_t cluster) {
    uint32_t fat_sector = fat_state.fat_begin_sector + (cluster / 128);
    uint32_t fat_offset = cluster % 128;
    uint32_t fat_buffer[128];

    if (sd_read_sector(fat_sector, (uint8_t *)fat_buffer) != 0) {
        return 0x0FFFFFFF;  /* End of chain on error */
    }

    return fat_buffer[fat_offset] & 0x0FFFFFFF;
}

/*
 * Convert filename to 8.3 format
 */
static void filename_to_83(const char *filename, char *name83) {
    int i, j;

    /* Initialize with spaces */
    for (i = 0; i < 11; i++) {
        name83[i] = ' ';
    }

    /* Copy name part (up to 8 chars) */
    for (i = 0; i < 8 && filename[i] && filename[i] != '.'; i++) {
        char c = filename[i];
        if (c >= 'a' && c <= 'z') c -= 32;  /* Uppercase */
        name83[i] = c;
    }

    /* Find and copy extension */
    const char *ext = filename;
    while (*ext && *ext != '.') ext++;
    if (*ext == '.') {
        ext++;
        for (j = 0; j < 3 && ext[j]; j++) {
            char c = ext[j];
            if (c >= 'a' && c <= 'z') c -= 32;
            name83[8 + j] = c;
        }
    }
}

/*
 * Compare two 8.3 names
 */
static int name83_compare(const char *a, const char *b) {
    for (int i = 0; i < 11; i++) {
        if (a[i] != b[i]) return 0;
    }
    return 1;
}

/*
 * Read a file from the filesystem
 */
int fat_read_file(const char *filename, uint32_t load_addr, uint32_t *size) {
    char name83[11];
    uint32_t dir_cluster;
    uint32_t dir_sector;
    uint8_t dir_buffer[512];
    fat_dir_entry_t *entries;
    uint32_t file_cluster = 0;
    uint32_t file_size = 0;
    int found = 0;

    if (!fat_state.initialized) {
        sd_debug("FAT: Not initialized\n");
        return -1;
    }

    sd_debug("FAT: Looking for file: ");
    uart_puts(filename);
    uart_puts("\n");

    /* Convert filename to 8.3 format */
    filename_to_83(filename, name83);

    /* Search root directory */
    dir_cluster = fat_state.root_dir_cluster;

    while (dir_cluster < 0x0FFFFFF8 && !found) {
        /* Read each sector in the cluster */
        dir_sector = cluster_to_sector(dir_cluster);

        for (uint32_t s = 0; s < fat_state.sectors_per_cluster && !found; s++) {
            if (sd_read_sector(dir_sector + s, dir_buffer) != 0) {
                sd_debug("FAT: Failed to read directory\n");
                return -1;
            }

            entries = (fat_dir_entry_t *)dir_buffer;

            /* Check each directory entry (16 per sector) */
            for (int i = 0; i < 16; i++) {
                /* End of directory */
                if (entries[i].name[0] == 0x00) {
                    sd_debug("FAT: File not found (end of dir)\n");
                    return -1;
                }

                /* Skip deleted entries */
                if ((uint8_t)entries[i].name[0] == 0xE5) continue;

                /* Skip long name entries and volume labels */
                if (entries[i].attributes == 0x0F) continue;
                if (entries[i].attributes & 0x08) continue;

                /* Check if name matches */
                if (name83_compare(entries[i].name, name83)) {
                    file_cluster = ((uint32_t)entries[i].first_cluster_high << 16) |
                                   entries[i].first_cluster_low;
                    file_size = entries[i].file_size;
                    found = 1;
                    sd_debug_hex("FAT: Found file, cluster: ", file_cluster);
                    sd_debug_hex("FAT: File size: ", file_size);
                    break;
                }
            }
        }

        /* Move to next directory cluster */
        dir_cluster = fat_get_next_cluster(dir_cluster);
    }

    if (!found) {
        sd_debug("FAT: File not found\n");
        return -1;
    }

    /* Read file data following cluster chain */
    uint8_t *dest = (uint8_t *)(uintptr_t)load_addr;
    uint32_t remaining = file_size;
    uint32_t cluster = file_cluster;

    while (remaining > 0 && cluster >= 2 && cluster < 0x0FFFFFF8) {
        uint32_t sector = cluster_to_sector(cluster);

        /* Read all sectors in this cluster */
        for (uint32_t s = 0; s < fat_state.sectors_per_cluster && remaining > 0; s++) {
            if (sd_read_sector(sector + s, sector_buffer) != 0) {
                sd_debug("FAT: Failed to read file data\n");
                return -1;
            }

            uint32_t to_copy = remaining > 512 ? 512 : remaining;
            for (uint32_t b = 0; b < to_copy; b++) {
                dest[b] = sector_buffer[b];
            }

            dest += to_copy;
            remaining -= to_copy;
        }

        /* Get next cluster */
        cluster = fat_get_next_cluster(cluster);
    }

    *size = file_size;
    sd_debug_hex("FAT: File loaded, bytes: ", file_size);

    return 0;
}
