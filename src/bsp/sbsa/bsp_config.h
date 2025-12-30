/*
 * ARM SBSA-Compatible Platform BSP Configuration
 * Platform-specific defines for the unified bootloader
 */

#ifndef BSP_CONFIG_H
#define BSP_CONFIG_H

/* RAM configuration for SBSA-compatible system
 * Placed at 1GB to stay within 4GB for reliable GOT operations
 */
#define RAM_BASE            0x40000000
#define RAM_SIZE            0x200000000     /* 8 GB max */

/* Peripheral base addresses (QEMU virt compatible) */
#define UART_BASE           0x09000000      /* PL011 UART */
#define GPIO_BASE           0x09030000      /* PL061 GPIO */
#define RTC_BASE            0x09010000      /* PL031 RTC */

/* PCIe/SMMU configuration */
#define PCIE_ECAM_BASE      0x4010000000ULL
#define SMMU_BASE           0x09050000

/* Timer configuration - ARM Generic Timer */
#define TIMER_FREQ          62500000        /* 62.5 MHz default */

/* Platform identification */
#define PLATFORM_NAME       "SBSA Compatible"
#define PLATFORM_DESC       "Server-Class Platform (8GB max)"

#endif /* BSP_CONFIG_H */
