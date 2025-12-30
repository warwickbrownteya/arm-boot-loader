/*
 * Raspberry Pi 3 BSP Configuration
 * Platform-specific defines for the unified bootloader
 */

#ifndef BSP_CONFIG_H
#define BSP_CONFIG_H

/* RAM configuration for Raspberry Pi 3 (BCM2837)
 * RAM starts at 0x0, but GPU loads kernel at 0x80000
 */
#define RAM_BASE            0x00000000
#define RAM_SIZE            0x40000000      /* 1 GB */

/* Peripheral base addresses (VideoCore legacy mapping) */
#define PERIPHERAL_BASE     0x3F000000
#define UART_BASE           0x3F201000      /* PL011 UART for QEMU */
#define GPIO_BASE           0x3F200000      /* GPIO */
#define SYSTIMER_BASE       0x3F003000      /* System Timer */
#define AUX_BASE            0x3F215000      /* Mini UART, SPI */

/* Timer frequency - BCM System Timer runs at 1MHz */
#define TIMER_FREQ          1000000

/* Platform identification */
#define PLATFORM_NAME       "Raspberry Pi 3"
#define PLATFORM_DESC       "BCM2837 - GPU-First Boot"

/* GPU loads ARM code at 0x80000 */
#define ENTRY_POINT         0x00080000

#endif /* BSP_CONFIG_H */
