/*
 * Xilinx Zynq UltraScale+ ZCU102 BSP Configuration
 * Platform-specific defines for the unified bootloader
 */

#ifndef BSP_CONFIG_H
#define BSP_CONFIG_H

/* RAM configuration for Zynq UltraScale+ */
#define RAM_BASE            0x00000000
#define RAM_SIZE            0x80000000      /* 2 GB DDR */

/* Peripheral base addresses */
#define UART_BASE           0xFF000000      /* Cadence UART0 */
#define GPIO_BASE           0xFF0A0000      /* GPIO controller */
#define TTC0_BASE           0xFF110000      /* Triple Timer Counter 0 */

/* Timer configuration - TTC runs at 100 MHz */
#define TIMER_FREQ          100000000

/* Platform identification */
#define PLATFORM_NAME       "Xilinx ZCU102"
#define PLATFORM_DESC       "Zynq UltraScale+ MPSoC Evaluation Kit"

#endif /* BSP_CONFIG_H */
