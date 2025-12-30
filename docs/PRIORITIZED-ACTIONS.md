# Prioritized Action Plan
## From Minimal QEMU Demo to Working Bootloader

**Date**: 2025-10-19
**Based on**: AUDIT-REPORT.md findings
**Philosophy**: Fix one thing at a time, test incrementally, maintain honesty

---

## Current State Summary

**What Works**: QEMU virt machine boot (5.4KB minimal bootloader)
**What Doesn't**: Physical hardware (Pi 4B tested, failed)
**Root Cause**: 82% of code not compiled + missing SD card firmware setup
**Goal**: Working boot on Raspberry Pi 4B

---

## Priority Levels

**P0 - CRITICAL**: Must fix to boot on any real hardware
**P1 - HIGH**: Core functionality needed for usable bootloader
**P2 - MEDIUM**: Important features, not immediately blocking
**P3 - LOW**: Nice-to-have enhancements

---

# P0 - CRITICAL: Get Hardware Boot Working (Week 1)

## P0.1 - SD Card Firmware Setup

**Estimated Time**: 30 minutes
**Complexity**: LOW (file copy + config creation)
**Blocker**: Yes - nothing works without this

### Action Steps

```bash
# 1. Insert SD card and identify mount point
diskutil list  # Find SD card (e.g., /dev/disk2)

# 2. Format SD card as FAT32 (if not already)
diskutil eraseDisk FAT32 PIBOOT MBR /dev/disk2

# 3. Copy GPU firmware files
cp /tmp/rpi_firmware/bootcode.bin /Volumes/PIBOOT/
cp /tmp/rpi_firmware/start4.elf /Volumes/PIBOOT/
cp /tmp/rpi_firmware/fixup4.dat /Volumes/PIBOOT/

# 4. Copy bootloader with correct name
cp bootloader.bin /Volumes/PIBOOT/kernel8.img

# 5. Create config.txt
cat > /Volumes/PIBOOT/config.txt <<'EOF'
# ARM 64-bit mode
arm_64bit=1

# Enable UART for debugging
enable_uart=1
uart_2ndstage=1

# Boot kernel
kernel=kernel8.img

# Reduce GPU memory (more for ARM CPU)
gpu_mem=16

# Optional: Set CPU frequency
#arm_freq=1500
EOF

# 6. Eject safely
diskutil unmount /Volumes/PIBOOT

# 7. Insert into Raspberry Pi 4B and test
```

**Expected Result**: UART output appears (even if garbled)

**Test**:
```bash
# Connect UART adapter:
# TX → GPIO14 (Pin 8)
# RX → GPIO15 (Pin 10)
# GND → GND (Pin 6)

# Monitor serial:
screen /dev/tty.usbserial-* 115200
```

**Success Criteria**: Any UART activity visible

---

## P0.2 - Fix Hardcoded BCM2837 Addresses

**Estimated Time**: 2 hours
**Complexity**: MEDIUM (requires understanding peripheral addressing)
**Blocker**: Yes - Pi 4 uses different addresses

### Problem

**Current code (uart.c:7)**:
```c
#define UART_BASE 0x3F201000  // BCM2837 ONLY - FAILS ON PI 4
```

**Pi 4B needs**: `0xFE201000` (BCM2711)

### Solution Option A: Quick Fix (For Pi 4 Testing)

**Edit uart.c, timer.c, gpio.c, mailbox.c**:
```c
// Change from:
#define UART_BASE 0x3F201000

// To:
#define UART_BASE 0xFE201000  // BCM2711 (Pi 4)
```

**Pro**: Fast, gets Pi 4 working
**Con**: Breaks QEMU, not portable

### Solution Option B: Runtime Detection (Proper Fix)

**Add to Makefile**:
```makefile
SRC_C = main.c uart.c timer.c gpio.c memory.c mailbox.c sd.c hardware.c
```

**Modify drivers to use hardware detection**:
```c
// uart.c
#include "hardware.h"

void uart_init(void) {
    uintptr_t uart_base = get_uart_base();  // Runtime detection
    // ... use uart_base instead of UART_BASE
}
```

**Pro**: Works on all Pi models
**Con**: Requires adding hardware.c (more work)

### Recommended: Start with Option A, then Option B

1. Quick test with hardcoded Pi 4 addresses (30 min)
2. If that works, add proper hardware detection (1.5 hrs)

---

## P0.3 - Fix Pointer Cast Warnings

**Estimated Time**: 30 minutes
**Complexity**: LOW (simple type changes)
**Blocker**: No (but improves code quality)

### Problem

```
uart.c:19: warning: cast to pointer from integer of different size
```

### Solution

**Change all drivers**:
```c
// Before:
static inline void mmio_write(uint32_t reg, uint32_t data) {
    *(volatile uint32_t*)reg = data;
}

// After:
static inline void mmio_write(uintptr_t reg, uint32_t data) {
    *(volatile uint32_t*)reg = data;
}
```

**Files to modify**: uart.c, timer.c, gpio.c, mailbox.c, sd.c

---

## P0.4 - First Hardware Boot Test

**Estimated Time**: 1 hour (including troubleshooting)
**Complexity**: MEDIUM (debugging unknown issues)
**Blocker**: This is the goal of P0

### Test Procedure

1. **Insert SD card into Pi 4B**
2. **Connect UART adapter**
3. **Open serial monitor**: `screen /dev/tty.usbserial-* 115200`
4. **Power on Pi 4B**
5. **Observe UART output**

### Expected Outcomes

**Best Case**: Full boot output
```
========================================
  Minimal ARM Bootloader v1.0
  Raspberry Pi 4B
========================================
...
```

**Good Case**: Garbled output (wrong baud rate)
- Try 9600, 38400, 57600, 230400

**Bad Case**: No output
- Check UART wiring
- Verify power LED solid
- Try different start*.elf files

**Failure Case**: No power
- Check power supply (5V 3A minimum)
- Try different SD card

### Debugging Steps

If no output:
1. Check power LED (should be solid red)
2. Check activity LED (should blink during boot)
3. Verify UART connections (TX/RX swapped?)
4. Try USB-serial adapter on different computer
5. Test SD card on computer (files visible?)
6. Check start4.elf MD5: `abd64bb7f65610815369c21f071da2de`

---

# P1 - HIGH: Core Functionality (Week 2)

## P1.1 - Add Hardware Abstraction Layer

**Estimated Time**: 4 hours
**Complexity**: MEDIUM
**Blocker**: No (but needed for multi-platform support)

### Action

**Update Makefile**:
```makefile
SRC_C = main.c uart.c timer.c gpio.c memory.c mailbox.c sd.c hardware.c hal.c
```

**Create hardware detection functions**:
```c
// hardware.c: Detect Pi model via mailbox
pi_model_t hardware_detect_model(void);
uintptr_t get_uart_base(void);
uintptr_t get_gpio_base(void);
uintptr_t get_timer_base(void);
```

**Update all drivers to use HAL**

**Test**: Boot on Pi 3B and Pi 4B, verify both work

---

## P1.2 - Add Interrupt Support

**Estimated Time**: 3 hours
**Complexity**: MEDIUM
**Blocker**: No (but needed for advanced I/O)

### Action

**Add to Makefile**:
```makefile
SRC_C = ... interrupt.c
```

**Implement basic IRQ handling**:
- Set up exception vectors
- Initialize GIC-400
- Register UART IRQ handler

**Test**: Interrupt-driven UART input

---

## P1.3 - Add Configuration Parser

**Estimated Time**: 3 hours
**Complexity**: MEDIUM
**Blocker**: No (but improves usability)

### Action

**Add to Makefile**:
```makefile
SRC_C = ... config.c
```

**Parse config.txt from SD card**:
- Read boot parameters
- Apply settings
- Log configuration

**Test**: Boot with custom config.txt settings

---

## P1.4 - Add Logging System

**Estimated Time**: 2 hours
**Complexity**: LOW
**Blocker**: No (but critical for debugging)

### Action

**Add to Makefile**:
```makefile
SRC_C = ... log.c
```

**Implement log levels**:
```c
log_debug("Initializing UART...");
log_info("Boot started");
log_warn("SD card slow");
log_error("Kernel not found");
```

**Test**: Boot with verbose logging

---

## P1.5 - Multi-Platform Testing

**Estimated Time**: 6 hours (if you have devices)
**Complexity**: MEDIUM
**Blocker**: No (but needed to claim "multi-platform support")

### Test Matrix

| Platform | Test Result | Issues Found | Fixed |
|----------|-------------|--------------|-------|
| QEMU virt | ✓ PASS | - | - |
| QEMU raspi3b | ? | ? | ? |
| Raspberry Pi 1 | UNTESTED | - | - |
| Raspberry Pi 3B | UNTESTED | - | - |
| Raspberry Pi 4B | ❌ FAIL | See P0 | Pending |
| Raspberry Pi Zero 2W | UNTESTED | - | - |

### Action

Test on at least 3 different Pi models, fix platform-specific issues

---

# P2 - MEDIUM: Important Features (Weeks 3-4)

## P2.1 - Fix SD Card Driver

**Estimated Time**: 6 hours
**Complexity**: HIGH
**Blocker**: No (but needed for kernel loading)

### Current Issue

SD card init fails in QEMU, untested on hardware

### Action

1. Test on real Pi hardware with actual SD card
2. Debug EMMC initialization sequence
3. Verify FAT32 parsing
4. Test file reading (kernel8.img)

**Test**: Successfully load kernel from SD card

---

## P2.2 - Add Additional Drivers

**Estimated Time**: 2-4 hours per driver
**Complexity**: MEDIUM
**Priority Order**:

1. **clock.c** - Clock management (HIGH)
2. **i2c.c** - I2C bus (MEDIUM)
3. **spi.c** - SPI bus (MEDIUM)
4. **pwm.c** - PWM output (LOW)
5. **dma.c** - DMA transfers (MEDIUM)
6. **watchdog.c** - Watchdog timer (MEDIUM)

### Action

Add drivers selectively based on actual needs:
- If using I2C sensors → Add i2c.c
- If using SPI devices → Add spi.c
- If need performance → Add dma.c
- If need reliability → Add watchdog.c

**Don't compile drivers you won't use** - keeps binary small

---

## P2.3 - Build Test Framework

**Estimated Time**: 8 hours
**Complexity**: MEDIUM
**Blocker**: No (but needed for quality)

### Action

**Add to Makefile** (separate test build):
```makefile
test: test_framework.o test_drivers.o
```

**Create unit tests**:
- Test UART initialization
- Test timer accuracy
- Test memory allocator
- Test GPIO functions
- Test mailbox interface

**Create integration tests**:
- Full boot sequence
- Driver interaction
- Error handling

**Run tests**:
```bash
make test
qemu-system-aarch64 -M virt -kernel test.bin -nographic
```

**Success Criteria**: >50% actual code coverage

---

## P2.4 - Add FSA State Machine

**Estimated Time**: 4 hours
**Complexity**: MEDIUM
**Blocker**: No (but makes boot process formal)

### Action

**Add to Makefile**:
```makefile
SRC_C = ... fsa_monitor.c
```

**Implement 44-state FSA**:
- Track current boot state
- Validate state transitions
- Log state changes
- Detect invalid transitions

**Test**: Boot with FSA monitoring, verify all states reached

---

## P2.5 - Performance Optimization

**Estimated Time**: 4 hours
**Complexity**: LOW
**Blocker**: No

### Action

1. **Measure boot time** (from power-on to kernel exec)
2. **Profile slow sections** (timer measurements)
3. **Optimize critical paths**:
   - UART buffer
   - SD card reads
   - Memory allocation
4. **Test**: Reduce boot time by 20%+

---

# P3 - LOW: Advanced Features (Month 2+)

## P3.1 - Security Features

**Estimated Time**: 16+ hours
**Complexity**: HIGH
**Blocker**: No (only needed if security required)

### Action

**Add to Makefile**:
```makefile
SRC_C = ... secure_boot.c security.c crypto.c verification.c
```

**Implement**:
- SHA-256 hashing
- Kernel signature verification
- Secure boot chain
- Boot attestation

**Test**: Verify kernel signatures before execution

---

## P3.2 - Network Boot (PXE/TFTP)

**Estimated Time**: 20+ hours
**Complexity**: HIGH
**Blocker**: No (advanced feature)

### Action

**Add to Makefile**:
```makefile
SRC_C = ... ethernet.c network.c network_protocols.c
```

**Implement**:
- Ethernet driver
- DHCP client
- TFTP client
- Network boot

**Test**: Boot kernel from network server

---

## P3.3 - USB Boot

**Estimated Time**: 16+ hours
**Complexity**: HIGH
**Blocker**: No (advanced feature)

### Action

**Add to Makefile**:
```makefile
SRC_C = ... usb.c
```

**Implement**:
- USB host controller
- Mass storage class
- USB boot

**Test**: Boot from USB drive

---

## P3.4 - Multi-Core Support

**Estimated Time**: 12+ hours
**Complexity**: HIGH
**Blocker**: No (optimization)

### Action

**Implement**:
- Secondary CPU startup
- Inter-processor interrupts
- Core affinity

**Test**: Boot all 4 cores on Pi 4

---

## P3.5 - Interactive Shell

**Estimated Time**: 8 hours
**Complexity**: MEDIUM
**Blocker**: No (nice-to-have)

### Action

**Add to Makefile**:
```makefile
SRC_C = ... shell.c
```

**Implement**:
- Command parser
- Built-in commands (boot, reset, help, info)
- UART input handling

**Test**: Interactive boot menu

---

# Summary Timeline

## Week 1: Get Hardware Working
- [ ] P0.1: SD card firmware setup (30 min)
- [ ] P0.2: Fix hardcoded addresses (2 hrs)
- [ ] P0.3: Fix pointer warnings (30 min)
- [ ] P0.4: Hardware boot test (1 hr)
**Goal**: Boot on Pi 4B

## Week 2: Core Functionality
- [ ] P1.1: Hardware abstraction (4 hrs)
- [ ] P1.2: Interrupt support (3 hrs)
- [ ] P1.3: Configuration parser (3 hrs)
- [ ] P1.4: Logging system (2 hrs)
- [ ] P1.5: Multi-platform testing (6 hrs)
**Goal**: Multi-platform support verified

## Weeks 3-4: Polish & Testing
- [ ] P2.1: Fix SD card driver (6 hrs)
- [ ] P2.2: Add needed drivers (8 hrs)
- [ ] P2.3: Build test framework (8 hrs)
- [ ] P2.4: Add FSA monitoring (4 hrs)
- [ ] P2.5: Performance optimization (4 hrs)
**Goal**: Production-quality basic bootloader

## Month 2+: Advanced Features (Optional)
- [ ] P3.1: Security features (16 hrs)
- [ ] P3.2: Network boot (20 hrs)
- [ ] P3.3: USB boot (16 hrs)
- [ ] P3.4: Multi-core (12 hrs)
- [ ] P3.5: Interactive shell (8 hrs)
**Goal**: Full-featured bootloader

---

# Quick Start: Next 3 Actions

If you want to start immediately:

## 1. Setup SD Card (30 minutes)
```bash
# See P0.1 above
```

## 2. Quick Test Current Code on Pi 4B (30 minutes)
Just to see what happens with current binary

## 3. Fix for Pi 4 and Retest (2 hours)
- Edit uart.c: Change UART_BASE to 0xFE201000
- Edit timer.c, gpio.c, mailbox.c similarly
- Rebuild
- Test again

---

# Decision Points

## Should You Add All 32 Unused Files?

**NO**. Add selectively:

**Add These (Core)**:
- ✅ hardware.c, hal.c (hardware abstraction)
- ✅ interrupt.c (IRQ support)
- ✅ config.c (configuration)
- ✅ log.c (debugging)
- ✅ clock.c (clock management)

**Add These If Needed**:
- ⚠️ i2c.c, spi.c (if using I2C/SPI devices)
- ⚠️ dma.c (if need performance)
- ⚠️ fsa_monitor.c (if want formal FSA)
- ⚠️ watchdog.c (if want reliability)

**Don't Add (Unless Specifically Needed)**:
- ❌ usb.c, ethernet.c, network.c (advanced features)
- ❌ secure_boot.c, crypto.c (unless security critical)
- ❌ boot_menu.c, shell.c (nice-to-have)
- ❌ test_*.c (separate test build)
- ❌ perfmon.c, memtest.c (diagnostic tools)

**Goal**: Bootloader that boots reliably, not feature bloat

---

# Success Metrics

## Milestone 1: Hardware Boot (Week 1)
- [x] Binary builds without errors
- [ ] UART output on Pi 4B
- [ ] Boot completes successfully
- [ ] Works on at least 1 physical Pi

## Milestone 2: Multi-Platform (Week 2)
- [ ] Works on 3+ Pi models
- [ ] Hardware abstraction working
- [ ] Interrupts functional
- [ ] Configuration parsing

## Milestone 3: Production Quality (Week 4)
- [ ] SD card loading works
- [ ] 50%+ actual test coverage
- [ ] FSA monitoring active
- [ ] Boot time < 3 seconds
- [ ] Documentation matches reality

## Milestone 4: Full-Featured (Month 2+)
- [ ] Network boot (if desired)
- [ ] USB boot (if desired)
- [ ] Security features (if needed)
- [ ] Multi-core (if wanted)

---

# Honest Assessment of Effort

**To fix hardware boot**: 1-2 days
**To add core features**: 1 week
**To reach production quality**: 2-4 weeks
**To add all 32 unused files**: Don't - be selective!

**Most important**: Test incrementally, update docs honestly, maintain scorecard

---

**Priority Order**:
1. Get it working on ONE physical Pi (P0)
2. Make it work on MULTIPLE Pi models (P1)
3. Add features ONLY as needed (P2/P3)
4. Keep binary small and focused

**Philosophy**: Working minimal > broken comprehensive

---

*See AUDIT-REPORT.md for detailed findings*
*See SCORECARD.md for current status tracking*
*See CHANGELOG-GUIDELINES.md for how to document progress*
