/* QEMU Virt Machine BSP Header */

#ifndef BSP_VIRT_H
#define BSP_VIRT_H

#include <stdint.h>

/* QEMU Virt Memory Map */
#define VIRT_FLASH0_BASE        0x00000000
#define VIRT_FLASH1_BASE        0x04000000
#define VIRT_GIC_DIST_BASE      0x08000000
#define VIRT_GIC_CPU_BASE       0x08010000
#define VIRT_GICV2M_BASE        0x08020000
#define VIRT_UART_BASE          0x09000000
#define VIRT_RTC_BASE           0x09010000
#define VIRT_FW_CFG_BASE        0x09020000
#define VIRT_GPIO_BASE          0x09030000
#define VIRT_VIRTIO_BASE        0x0A000000
#define VIRT_PCIE_MMIO_BASE     0x10000000
#define VIRT_RAM_BASE           0x40000000
#define VIRT_RAM_SIZE           0x08000000  /* 128MB default */

/* PL011 UART Registers */
#define PL011_DR                0x00    /* Data Register */
#define PL011_RSR               0x04    /* Receive Status Register */
#define PL011_FR                0x18    /* Flag Register */
#define PL011_ILPR              0x20    /* IrDA Low-Power Counter */
#define PL011_IBRD              0x24    /* Integer Baud Rate */
#define PL011_FBRD              0x28    /* Fractional Baud Rate */
#define PL011_LCR_H             0x2C    /* Line Control */
#define PL011_CR                0x30    /* Control Register */
#define PL011_IFLS              0x34    /* Interrupt FIFO Level */
#define PL011_IMSC              0x38    /* Interrupt Mask */
#define PL011_RIS               0x3C    /* Raw Interrupt Status */
#define PL011_MIS               0x40    /* Masked Interrupt Status */
#define PL011_ICR               0x44    /* Interrupt Clear */

/* PL011 Flag Register bits */
#define PL011_FR_TXFE           (1 << 7)    /* TX FIFO Empty */
#define PL011_FR_RXFF           (1 << 6)    /* RX FIFO Full */
#define PL011_FR_TXFF           (1 << 5)    /* TX FIFO Full */
#define PL011_FR_RXFE           (1 << 4)    /* RX FIFO Empty */
#define PL011_FR_BUSY           (1 << 3)    /* UART Busy */

/* PL011 Line Control bits */
#define PL011_LCR_H_WLEN_8      (3 << 5)    /* 8 bits */
#define PL011_LCR_H_FEN         (1 << 4)    /* FIFO Enable */

/* PL011 Control Register bits */
#define PL011_CR_RXE            (1 << 9)    /* Receive Enable */
#define PL011_CR_TXE            (1 << 8)    /* Transmit Enable */
#define PL011_CR_UARTEN         (1 << 0)    /* UART Enable */

/* PL031 RTC Registers */
#define PL031_DR                0x00    /* Data Register */
#define PL031_MR                0x04    /* Match Register */
#define PL031_LR                0x08    /* Load Register */
#define PL031_CR                0x0C    /* Control Register */

/* PL061 GPIO Registers */
#define PL061_DATA              0x000   /* Data Register (0x000-0x3FC) */
#define PL061_DIR               0x400   /* Direction Register */
#define PL061_IS                0x404   /* Interrupt Sense */
#define PL061_IBE               0x408   /* Interrupt Both Edges */
#define PL061_IEV               0x40C   /* Interrupt Event */
#define PL061_IE                0x410   /* Interrupt Mask */
#define PL061_RIS               0x414   /* Raw Interrupt Status */
#define PL061_MIS               0x418   /* Masked Interrupt Status */
#define PL061_IC                0x41C   /* Interrupt Clear */
#define PL061_AFSEL             0x420   /* Alternate Function Select */

/* ARM Generic Timer - accessed via system registers */
/* CNTFRQ_EL0  - Counter Frequency */
/* CNTPCT_EL0  - Physical Counter */
/* CNTP_TVAL_EL0 - Timer Value */
/* CNTP_CTL_EL0  - Timer Control */

#endif /* BSP_VIRT_H */
