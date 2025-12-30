/*
 * UART wrapper header for Raspberry Pi BSP
 * Maps generic UART functions to raspi-specific implementations
 */

#ifndef UART_H
#define UART_H

#include "bsp_raspi.h"

/* Map generic functions to raspi-specific */
#define uart_init()         raspi_uart_init()
#define uart_putc(c)        raspi_uart_putc(c)
#define uart_puts(s)        raspi_uart_puts(s)
#define uart_getc()         raspi_uart_getc()

#endif /* UART_H */
