/* Hardware Abstraction Layer - Ultra Simple */

#include <stdint.h>
#include "hardware.h"

/* Get UART base address - hardcoded for BCM2837 */
uintptr_t get_uart_base(void) {
    return 0x3F201000;
}
