/* ARM Versatile Express A15 BSP Header */

#ifndef BSP_VEXPRESS_H
#define BSP_VEXPRESS_H

#include <stdint.h>

/* Versatile Express A15 Memory Map */
#define VEXPRESS_NOR_FLASH_BASE     0x00000000
#define VEXPRESS_NOR_FLASH_SIZE     0x04000000  /* 64MB */
#define VEXPRESS_PSRAM_BASE         0x08000000
#define VEXPRESS_PSRAM_SIZE         0x04000000  /* 64MB */
#define VEXPRESS_VRAM_BASE          0x18000000
#define VEXPRESS_VRAM_SIZE          0x02000000  /* 32MB */
#define VEXPRESS_PERIPH_BASE        0x1C000000
#define VEXPRESS_DRAM_BASE          0x80000000
#define VEXPRESS_DRAM_SIZE          0x40000000  /* 1GB */

/* Peripheral Addresses */
#define VEXPRESS_SYSREG_BASE        0x1C010000  /* System Registers */
#define VEXPRESS_SP810_BASE         0x1C020000  /* System Controller */
#define VEXPRESS_SERIAL_BASE        0x1C090000  /* PL011 UART0 */
#define VEXPRESS_SERIAL1_BASE       0x1C0A0000  /* PL011 UART1 */
#define VEXPRESS_SERIAL2_BASE       0x1C0B0000  /* PL011 UART2 */
#define VEXPRESS_SERIAL3_BASE       0x1C0C0000  /* PL011 UART3 */
#define VEXPRESS_TIMER_BASE         0x1C110000  /* SP804 Timer */
#define VEXPRESS_TIMER2_BASE        0x1C120000  /* SP804 Timer 2 */
#define VEXPRESS_RTC_BASE           0x1C170000  /* PL031 RTC */
#define VEXPRESS_MMC_BASE           0x1C050000  /* PL180 MMC */
#define VEXPRESS_KMI0_BASE          0x1C060000  /* PL050 KMI (Keyboard) */
#define VEXPRESS_KMI1_BASE          0x1C070000  /* PL050 KMI (Mouse) */
#define VEXPRESS_CLCD_BASE          0x1C1F0000  /* PL111 CLCD */

/* GIC (Generic Interrupt Controller) */
#define VEXPRESS_GIC_DIST_BASE      0x2C001000  /* GIC Distributor */
#define VEXPRESS_GIC_CPU_BASE       0x2C002000  /* GIC CPU Interface */

/* PL011 UART Registers (same as virt) */
#define PL011_DR                    0x00    /* Data Register */
#define PL011_RSR                   0x04    /* Receive Status Register */
#define PL011_FR                    0x18    /* Flag Register */
#define PL011_ILPR                  0x20    /* IrDA Low-Power Counter */
#define PL011_IBRD                  0x24    /* Integer Baud Rate */
#define PL011_FBRD                  0x28    /* Fractional Baud Rate */
#define PL011_LCR_H                 0x2C    /* Line Control */
#define PL011_CR                    0x30    /* Control Register */
#define PL011_IFLS                  0x34    /* Interrupt FIFO Level */
#define PL011_IMSC                  0x38    /* Interrupt Mask */
#define PL011_RIS                   0x3C    /* Raw Interrupt Status */
#define PL011_MIS                   0x40    /* Masked Interrupt Status */
#define PL011_ICR                   0x44    /* Interrupt Clear */

/* PL011 Flag Register bits */
#define PL011_FR_TXFE               (1 << 7)    /* TX FIFO Empty */
#define PL011_FR_RXFF               (1 << 6)    /* RX FIFO Full */
#define PL011_FR_TXFF               (1 << 5)    /* TX FIFO Full */
#define PL011_FR_RXFE               (1 << 4)    /* RX FIFO Empty */
#define PL011_FR_BUSY               (1 << 3)    /* UART Busy */

/* PL011 Line Control bits */
#define PL011_LCR_H_WLEN_8          (3 << 5)    /* 8 bits */
#define PL011_LCR_H_FEN             (1 << 4)    /* FIFO Enable */

/* PL011 Control Register bits */
#define PL011_CR_RXE                (1 << 9)    /* Receive Enable */
#define PL011_CR_TXE                (1 << 8)    /* Transmit Enable */
#define PL011_CR_UARTEN             (1 << 0)    /* UART Enable */

/* SP804 Dual Timer Registers */
#define SP804_TIMER1_LOAD           0x00    /* Timer 1 Load */
#define SP804_TIMER1_VALUE          0x04    /* Timer 1 Value (RO) */
#define SP804_TIMER1_CONTROL        0x08    /* Timer 1 Control */
#define SP804_TIMER1_INTCLR         0x0C    /* Timer 1 Interrupt Clear (WO) */
#define SP804_TIMER1_RIS            0x10    /* Timer 1 Raw Interrupt Status (RO) */
#define SP804_TIMER1_MIS            0x14    /* Timer 1 Masked Interrupt Status (RO) */
#define SP804_TIMER1_BGLOAD         0x18    /* Timer 1 Background Load */

#define SP804_TIMER2_LOAD           0x20    /* Timer 2 Load */
#define SP804_TIMER2_VALUE          0x24    /* Timer 2 Value (RO) */
#define SP804_TIMER2_CONTROL        0x28    /* Timer 2 Control */
#define SP804_TIMER2_INTCLR         0x2C    /* Timer 2 Interrupt Clear (WO) */
#define SP804_TIMER2_RIS            0x30    /* Timer 2 Raw Interrupt Status (RO) */
#define SP804_TIMER2_MIS            0x34    /* Timer 2 Masked Interrupt Status (RO) */
#define SP804_TIMER2_BGLOAD         0x38    /* Timer 2 Background Load */

/* SP804 Control Register bits */
#define SP804_CTRL_ENABLE           (1 << 7)    /* Timer Enable */
#define SP804_CTRL_PERIODIC         (1 << 6)    /* Periodic Mode */
#define SP804_CTRL_INTEN            (1 << 5)    /* Interrupt Enable */
#define SP804_CTRL_PRESCALE_1       (0 << 2)    /* Prescale /1 */
#define SP804_CTRL_PRESCALE_16      (1 << 2)    /* Prescale /16 */
#define SP804_CTRL_PRESCALE_256     (2 << 2)    /* Prescale /256 */
#define SP804_CTRL_32BIT            (1 << 1)    /* 32-bit mode */
#define SP804_CTRL_ONESHOT          (1 << 0)    /* One-shot mode */

/* SP804 Timer Clock: 1MHz on Versatile Express */
#define SP804_CLOCK_FREQ            1000000

/* System Register offsets */
#define SYSREG_ID                   0x00    /* Board ID */
#define SYSREG_SW                   0x04    /* Switch states */
#define SYSREG_LED                  0x08    /* LED outputs */
#define SYSREG_OSC0                 0x0C    /* Oscillator 0 control */
#define SYSREG_OSC1                 0x10    /* Oscillator 1 control */
#define SYSREG_OSC2                 0x14    /* Oscillator 2 control */
#define SYSREG_100HZ                0x24    /* 100Hz counter */
#define SYSREG_FLAGS                0x30    /* Flags register */
#define SYSREG_FLAGSCLR             0x34    /* Flags clear */
#define SYSREG_NVFLAGS              0x38    /* Non-volatile flags */
#define SYSREG_NVFLAGSCLR           0x3C    /* Non-volatile flags clear */
#define SYSREG_RESETCTL             0x40    /* Reset control */
#define SYSREG_PROC_ID0             0x84    /* Processor ID */
#define SYSREG_SYS_CFGDATA          0xA0    /* Config data */
#define SYSREG_SYS_CFGCTRL          0xA4    /* Config control */
#define SYSREG_SYS_CFGSTAT          0xA8    /* Config status */

#endif /* BSP_VEXPRESS_H */
