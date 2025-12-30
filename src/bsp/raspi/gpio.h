/*
 * GPIO wrapper header for Raspberry Pi BSP
 * Maps generic GPIO functions to raspi-specific implementations
 */

#ifndef GPIO_H
#define GPIO_H

#include "bsp_raspi.h"

/* Map generic functions to raspi-specific */
#define gpio_init()                 raspi_gpio_init()
#define gpio_set_function(p,f)      raspi_gpio_set_function(p,f)
#define gpio_set(p)                 raspi_gpio_set(p)
#define gpio_clear(p)               raspi_gpio_clear(p)
#define gpio_read(p)                raspi_gpio_read(p)

#endif /* GPIO_H */
