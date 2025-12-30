/* ARM SBSA-Compatible Platform BSP Header */

#ifndef BSP_SBSA_H
#define BSP_SBSA_H

#include <stdint.h>

/*
 * SBSA-Compatible Memory Map
 * ==========================
 * This BSP targets SBSA-class server platforms with addresses within 8GB.
 * Uses QEMU 'virt' machine peripheral layout for testing compatibility.
 *
 * WHY NOT QEMU sbsa-ref (1TB RAM)?
 * --------------------------------
 * QEMU's sbsa-ref places RAM at 0x10000000000 (1TB), causing AArch64
 * GOT relocation failures. The ADRP instruction only supports ~4GB
 * PC-relative range, so string literal lookups via GOT corrupt at 1TB.
 *
 * This configuration uses 0x40000000 (1GB) RAM base, supporting systems
 * with up to 8GB RAM while staying within reliable addressing range.
 */

/* Peripheral I/O - QEMU virt machine compatible */
#define SBSA_UART_BASE          0x09000000ULL   /* PL011 UART */
#define SBSA_UART_SIZE          0x00001000ULL
#define SBSA_RTC_BASE           0x09010000ULL   /* PL031 RTC */
#define SBSA_RTC_SIZE           0x00001000ULL
#define SBSA_GPIO_BASE          0x09030000ULL   /* PL061 GPIO */
#define SBSA_GPIO_SIZE          0x00001000ULL

/* GIC v3 - QEMU virt machine layout */
#define SBSA_GIC_DIST_BASE      0x08000000ULL
#define SBSA_GIC_DIST_SIZE      0x00010000ULL
#define SBSA_GIC_REDIST_BASE    0x080A0000ULL
#define SBSA_GIC_REDIST_SIZE    0x00F60000ULL

/* PCIe - QEMU virt machine layout */
#define SBSA_PCIE_ECAM_BASE     0x4010000000ULL /* Config space */
#define SBSA_PCIE_ECAM_SIZE     0x10000000ULL   /* 256MB */
#define SBSA_PCIE_MMIO_BASE     0x10000000ULL   /* Memory mapped I/O */
#define SBSA_PCIE_MMIO_SIZE     0x2EFF0000ULL

/* System RAM - Within 4GB for GOT compatibility */
#define SBSA_RAM_BASE           0x40000000ULL   /* 1GB offset */
#define SBSA_RAM_SIZE           0x200000000ULL  /* 8GB max supported */

/* Legacy sbsa-ref addresses (for reference, not used) */
#define SBSA_REF_RAM_BASE       0x10000000000ULL  /* 1TB - causes GOT issues */
#define SBSA_SMMU_BASE          0x09050000ULL     /* System MMU placeholder */

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

/* SBSA-specific functions */
uint32_t sbsa_get_system_id(void);
uint32_t sbsa_get_gic_version(void);
uint64_t sbsa_get_pcie_ecam_base(void);
uint64_t sbsa_get_smmu_base(void);

/* Additional address accessors (avoid GOT relocation issues) */
uint64_t sbsa_get_ram_base(void);
uint64_t sbsa_get_ram_size(void);
uint64_t sbsa_get_uart_base(void);
uint64_t sbsa_get_gpio_base(void);

#endif /* BSP_SBSA_H */
