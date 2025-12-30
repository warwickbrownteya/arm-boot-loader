/*
 * Memory wrapper header for Raspberry Pi BSP
 * Maps generic memory functions to raspi-specific implementations
 */

#ifndef MEMORY_H
#define MEMORY_H

#include "bsp_raspi.h"

/* Map generic functions to raspi-specific */
#define mem_alloc(size)     raspi_malloc(size)
#define mem_free(ptr)       raspi_free(ptr)

#endif /* MEMORY_H */
