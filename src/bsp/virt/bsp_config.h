/*
 * QEMU Virt Machine BSP Configuration
 * Platform-specific defines for the unified bootloader
 */

#ifndef BSP_CONFIG_H
#define BSP_CONFIG_H

/* RAM configuration for QEMU virt machine */
#define RAM_BASE            0x40000000
#define RAM_SIZE            0x10000000      /* 256 MB default */

/* Peripheral base addresses */
#define UART_BASE           0x09000000      /* PL011 UART */
#define GPIO_BASE           0x09030000      /* PL061 GPIO */
#define RTC_BASE            0x09010000      /* PL031 RTC */

/* Timer configuration - ARM Generic Timer */
#define TIMER_FREQ          62500000        /* 62.5 MHz */

/* Platform identification */
#define PLATFORM_NAME       "QEMU Virt"
#define PLATFORM_DESC       "QEMU ARM Virtual Machine"

#endif /* BSP_CONFIG_H */
