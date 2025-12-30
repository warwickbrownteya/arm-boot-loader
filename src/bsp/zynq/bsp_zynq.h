/* Xilinx Zynq UltraScale+ ZCU102 BSP Header */

#ifndef BSP_ZYNQ_H
#define BSP_ZYNQ_H

#include <stdint.h>

/* Zynq UltraScale+ Memory Map */
#define ZYNQ_OCM_BASE           0x00000000      /* On-Chip Memory (256KB) */
#define ZYNQ_OCM_SIZE           0x00040000
#define ZYNQ_DDR_LOW_BASE       0x00000000      /* DDR Low (2GB) */
#define ZYNQ_DDR_LOW_SIZE       0x80000000
#define ZYNQ_DDR_HIGH_BASE      0x800000000ULL  /* DDR High */

/* Peripheral Base Addresses */
#define ZYNQ_UART0_BASE         0xFF000000
#define ZYNQ_UART1_BASE         0xFF010000
#define ZYNQ_I2C0_BASE          0xFF020000
#define ZYNQ_I2C1_BASE          0xFF030000
#define ZYNQ_SPI0_BASE          0xFF040000
#define ZYNQ_SPI1_BASE          0xFF050000
#define ZYNQ_CAN0_BASE          0xFF060000
#define ZYNQ_CAN1_BASE          0xFF070000
#define ZYNQ_GPIO_BASE          0xFF0A0000
#define ZYNQ_GEM0_BASE          0xFF0B0000      /* Ethernet */
#define ZYNQ_GEM1_BASE          0xFF0C0000
#define ZYNQ_GEM2_BASE          0xFF0D0000
#define ZYNQ_GEM3_BASE          0xFF0E0000
#define ZYNQ_QSPI_BASE          0xFF0F0000
#define ZYNQ_TTC0_BASE          0xFF110000      /* Triple Timer Counter */
#define ZYNQ_TTC1_BASE          0xFF120000
#define ZYNQ_TTC2_BASE          0xFF130000
#define ZYNQ_TTC3_BASE          0xFF140000
#define ZYNQ_SD0_BASE           0xFF160000      /* SDHCI */
#define ZYNQ_SD1_BASE           0xFF170000
#define ZYNQ_RTC_BASE           0xFFA60000
#define ZYNQ_GIC_DIST_BASE      0xF9010000
#define ZYNQ_GIC_CPU_BASE       0xF9020000

/* Cadence UART Registers */
#define UART_CR                 0x00    /* Control Register */
#define UART_MR                 0x04    /* Mode Register */
#define UART_IER                0x08    /* Interrupt Enable Register */
#define UART_IDR                0x0C    /* Interrupt Disable Register */
#define UART_IMR                0x10    /* Interrupt Mask Register */
#define UART_ISR                0x14    /* Interrupt Status Register */
#define UART_BAUDGEN            0x18    /* Baud Rate Generator */
#define UART_RXTOUT             0x1C    /* RX Timeout Register */
#define UART_RXWM               0x20    /* RX FIFO Trigger Level */
#define UART_MODEMCR            0x24    /* Modem Control Register */
#define UART_MODEMSR            0x28    /* Modem Status Register */
#define UART_SR                 0x2C    /* Channel Status Register */
#define UART_FIFO               0x30    /* TX/RX FIFO */
#define UART_BAUDDIV            0x34    /* Baud Rate Divider */
#define UART_FLOWDEL            0x38    /* Flow Control Delay */
#define UART_TXWM               0x44    /* TX FIFO Trigger Level */

/* UART Control Register bits */
#define UART_CR_STOPBRK         (1 << 8)
#define UART_CR_STTBRK          (1 << 7)
#define UART_CR_RSTTO           (1 << 6)
#define UART_CR_TXDIS           (1 << 5)
#define UART_CR_TXEN            (1 << 4)
#define UART_CR_RXDIS           (1 << 3)
#define UART_CR_RXEN            (1 << 2)
#define UART_CR_TXRST           (1 << 1)
#define UART_CR_RXRST           (1 << 0)

/* UART Mode Register bits */
#define UART_MR_CHMODE_NORM     (0 << 8)
#define UART_MR_CHMODE_ECHO     (1 << 8)
#define UART_MR_CHMODE_LLOOP    (2 << 8)
#define UART_MR_CHMODE_RLOOP    (3 << 8)
#define UART_MR_NBSTOP_1        (0 << 6)
#define UART_MR_NBSTOP_1_5      (1 << 6)
#define UART_MR_NBSTOP_2        (2 << 6)
#define UART_MR_PAR_EVEN        (0 << 3)
#define UART_MR_PAR_ODD         (1 << 3)
#define UART_MR_PAR_SPACE       (2 << 3)
#define UART_MR_PAR_MARK        (3 << 3)
#define UART_MR_PAR_NONE        (4 << 3)
#define UART_MR_CHARLEN_8       (0 << 1)
#define UART_MR_CHARLEN_7       (2 << 1)
#define UART_MR_CHARLEN_6       (3 << 1)
#define UART_MR_CLKSEL          (1 << 0)

/* UART Status Register bits */
#define UART_SR_TNFUL           (1 << 14)   /* TX FIFO Nearly Full */
#define UART_SR_TTRIG           (1 << 13)   /* TX FIFO Trigger */
#define UART_SR_FLOWDEL         (1 << 12)   /* RX Flow Delay */
#define UART_SR_TACTIVE         (1 << 11)   /* TX Active */
#define UART_SR_RACTIVE         (1 << 10)   /* RX Active */
#define UART_SR_TXFULL          (1 << 4)    /* TX FIFO Full */
#define UART_SR_TXEMPTY         (1 << 3)    /* TX FIFO Empty */
#define UART_SR_RXFULL          (1 << 2)    /* RX FIFO Full */
#define UART_SR_RXEMPTY         (1 << 1)    /* RX FIFO Empty */
#define UART_SR_RTRIG           (1 << 0)    /* RX FIFO Trigger */

/* Triple Timer Counter Registers */
#define TTC_CLK_CTRL            0x00    /* Clock Control */
#define TTC_CNT_CTRL            0x0C    /* Counter Control */
#define TTC_CNT_VAL             0x18    /* Counter Value */
#define TTC_INTERVAL_VAL        0x24    /* Interval Value */
#define TTC_MATCH_0             0x30    /* Match 0 */
#define TTC_MATCH_1             0x3C    /* Match 1 */
#define TTC_MATCH_2             0x48    /* Match 2 */
#define TTC_ISR                 0x54    /* Interrupt Status */
#define TTC_IER                 0x60    /* Interrupt Enable */

/* TTC Counter Control bits */
#define TTC_CNT_CTRL_DIS        (1 << 0)    /* Disable */
#define TTC_CNT_CTRL_INT        (1 << 1)    /* Interval mode */
#define TTC_CNT_CTRL_DEC        (1 << 2)    /* Decrement */
#define TTC_CNT_CTRL_MATCH      (1 << 3)    /* Match mode */
#define TTC_CNT_CTRL_RST        (1 << 4)    /* Reset */

/* GPIO Registers */
#define GPIO_MASK_DATA_0_LSW    0x000
#define GPIO_MASK_DATA_0_MSW    0x004
#define GPIO_MASK_DATA_1_LSW    0x008
#define GPIO_MASK_DATA_1_MSW    0x00C
#define GPIO_DATA_0             0x040
#define GPIO_DATA_1             0x044
#define GPIO_DIRM_0             0x204   /* Direction Mode Bank 0 */
#define GPIO_OEN_0              0x208   /* Output Enable Bank 0 */
#define GPIO_DIRM_1             0x244   /* Direction Mode Bank 1 */
#define GPIO_OEN_1              0x248   /* Output Enable Bank 1 */

#endif /* BSP_ZYNQ_H */
