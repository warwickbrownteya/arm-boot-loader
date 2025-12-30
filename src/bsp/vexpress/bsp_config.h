/*
 * ARM Versatile Express A15 BSP Configuration
 * Platform-specific defines for the unified bootloader (ARMv7-A 32-bit)
 */

#ifndef BSP_CONFIG_H
#define BSP_CONFIG_H

/* RAM configuration for Versatile Express */
#define RAM_BASE            0x80000000
#define RAM_SIZE            0x40000000      /* 1 GB */

/* Peripheral base addresses */
#define UART_BASE           0x1C090000      /* PL011 UART */
#define TIMER_BASE          0x1C110000      /* SP804 Timer */
#define SYSREG_BASE         0x1C010000      /* System registers (LEDs, switches) */

/* Timer configuration - SP804 runs at 1 MHz */
#define TIMER_FREQ          1000000

/* Platform identification */
#define PLATFORM_NAME       "Versatile Express A15"
#define PLATFORM_DESC       "ARM Versatile Express for Cortex-A15"

#endif /* BSP_CONFIG_H */
