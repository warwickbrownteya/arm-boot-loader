/* Minimal Timer Implementation for Raspberry Pi 3/4 */

#include <stdint.h>
#include "timer.h"

// Peripheral base (Pi 3: 0x3F000000, Pi 4: 0xFE000000)
#ifndef PERIPHERAL_BASE
#define PERIPHERAL_BASE 0x3F000000
#endif

#define TIMER_BASE (PERIPHERAL_BASE + 0x003000)

#define TIMER_CS  (TIMER_BASE + 0x00)  // Control/Status
#define TIMER_CLO (TIMER_BASE + 0x04)  // Counter Lower 32 bits
#define TIMER_CHI (TIMER_BASE + 0x08)  // Counter Higher 32 bits

static inline uint32_t mmio_read(uint64_t reg) {
    return *(volatile uint32_t*)(uintptr_t)reg;
}

void timer_init(void) {
    // System timer is always running on Pi, no init needed
    // Just verify we can read it
    (void)mmio_read(TIMER_CLO);
}

uint64_t timer_get_ticks(void) {
    uint32_t hi, lo;

    // Read high, then low, then high again to handle rollover
    do {
        hi = mmio_read(TIMER_CHI);
        lo = mmio_read(TIMER_CLO);
    } while (hi != mmio_read(TIMER_CHI));

    return ((uint64_t)hi << 32) | lo;
}

void timer_delay_us(uint32_t microseconds) {
    uint64_t start = timer_get_ticks();
    uint64_t end = start + microseconds;

    // Handle 64-bit rollover (very unlikely but safe)
    if (end < start) {
        while (timer_get_ticks() >= start);  // Wait for rollover
        while (timer_get_ticks() < end);     // Wait for target
    } else {
        while (timer_get_ticks() < end);     // Normal case
    }
}

void timer_delay_ms(uint32_t milliseconds) {
    timer_delay_us(milliseconds * 1000);
}
