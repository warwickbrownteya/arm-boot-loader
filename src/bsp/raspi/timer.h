/*
 * Timer wrapper header for Raspberry Pi BSP
 * Maps generic timer functions to raspi-specific implementations
 */

#ifndef TIMER_H
#define TIMER_H

#include "bsp_raspi.h"

/* Map generic functions to raspi-specific */
#define timer_init()            raspi_timer_init()
#define timer_get_ticks()       raspi_timer_get_ticks()
#define timer_delay_us(us)      raspi_timer_delay_us(us)
#define timer_delay_ms(ms)      raspi_timer_delay_ms(ms)

#endif /* TIMER_H */
