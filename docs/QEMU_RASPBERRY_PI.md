# QEMU Raspberry Pi Emulation - Complete Guide

**QEMU Version:** 10.1.1
**Date:** October 18, 2025
**Project:** ARM64 Bare-Metal Bootloader

---

## Overview

QEMU provides emulation for **6 Raspberry Pi models** spanning the entire product line from Pi Zero to Pi 4B. This guide covers all supported models, their capabilities, limitations, and usage for bare-metal development.

---

## Supported Raspberry Pi Models

| Model | Machine ID | SoC | CPU Core | CPU Count | RAM | Bit Width | QEMU Binary |
|-------|------------|-----|----------|-----------|-----|-----------|-------------|
| **Pi Zero** | `raspi0` | BCM2835 | ARM1176JZF-S | 1 | 512 MB | 32-bit | qemu-system-arm / aarch64 |
| **Pi 1 A+** | `raspi1ap` | BCM2835 | ARM1176JZF-S | 1 | 512 MB | 32-bit | qemu-system-arm / aarch64 |
| **Pi 2B** | `raspi2b` | BCM2836 | Cortex-A7 | 4 | 1 GB | 32-bit | qemu-system-arm / aarch64 |
| **Pi 3A+** | `raspi3ap` | BCM2837B0 | Cortex-A53 | 4 | 512 MB | 64-bit | qemu-system-aarch64 only |
| **Pi 3B** | `raspi3b` | BCM2837 | Cortex-A53 | 4 | 1 GB | 64-bit | qemu-system-aarch64 only ✅ |
| **Pi 4B** | `raspi4b` | BCM2711 | Cortex-A72 | 4 | up to 8 GB | 64-bit | qemu-system-aarch64 only |

**Legend:**
- ✅ = Model used in this bootloader project
- All models support both 32-bit and 64-bit kernels (except where noted)

---

## Model Details

### 1. Raspberry Pi Zero / 1 A+ (BCM2835)

**Machine IDs:** `raspi0`, `raspi1ap`

#### Hardware Specifications
- **CPU:** ARM1176JZF-S (ARMv6 architecture)
- **Cores:** Single core
- **Clock Speed:** 1 GHz (Zero), 700 MHz (1A+)
- **RAM:** 512 MB
- **GPU:** VideoCore IV
- **Peripheral Base:** 0x20000000

#### QEMU Support
```bash
# Boot with ARM emulator (32-bit)
qemu-system-arm -M raspi0 -kernel kernel.img -nographic

# Boot with AArch64 emulator (32-bit mode)
qemu-system-aarch64 -M raspi0 -kernel kernel.img -nographic
```

#### Emulated Peripherals
- ✅ UART (PL011)
- ✅ System Timer
- ✅ GPIO (limited)
- ⚠️ EMMC/SD (basic)
- ❌ USB
- ❌ HDMI
- ❌ CSI Camera

#### Use Cases
- Legacy ARM development
- ARMv6 instruction set testing
- Minimal embedded systems
- Educational purposes

---

### 2. Raspberry Pi 2B (BCM2836)

**Machine ID:** `raspi2b`

#### Hardware Specifications
- **CPU:** ARM Cortex-A7 (ARMv7 architecture)
- **Cores:** 4 cores (quad-core)
- **Clock Speed:** 900 MHz
- **RAM:** 1 GB
- **GPU:** VideoCore IV
- **Peripheral Base:** 0x3F000000

#### QEMU Support
```bash
# Boot with ARM emulator (32-bit)
qemu-system-arm -M raspi2b -kernel kernel7.img -nographic

# Boot with AArch64 emulator (32-bit mode)
qemu-system-aarch64 -M raspi2b -kernel kernel7.img -nographic

# Multi-core boot
qemu-system-arm -M raspi2b -smp 4 -kernel kernel7.img -nographic
```

#### Emulated Peripherals
- ✅ UART (PL011)
- ✅ System Timer
- ✅ GPIO (improved)
- ⚠️ EMMC/SD (basic)
- ⚠️ Mailbox (limited)
- ❌ USB
- ❌ HDMI
- ❌ Ethernet

#### Use Cases
- Multi-core ARM development
- ARMv7 architecture testing
- SMP (symmetric multiprocessing) testing
- 32-bit OS development

---

### 3. Raspberry Pi 3A+ (BCM2837B0)

**Machine ID:** `raspi3ap`

#### Hardware Specifications
- **CPU:** ARM Cortex-A53 (ARMv8-A 64-bit)
- **Cores:** 4 cores (quad-core)
- **Clock Speed:** 1.4 GHz
- **RAM:** 512 MB
- **GPU:** VideoCore IV
- **Peripheral Base:** 0x3F000000

#### QEMU Support
```bash
# Boot with AArch64 emulator (64-bit kernel)
qemu-system-aarch64 -M raspi3ap -kernel kernel8.img -nographic

# Multi-core boot
qemu-system-aarch64 -M raspi3ap -smp 4 -kernel kernel8.img -nographic

# With memory limit
qemu-system-aarch64 -M raspi3ap -m 512M -kernel kernel8.img -nographic
```

#### Emulated Peripherals
- ✅ UART (PL011 and mini UART)
- ✅ System Timer
- ✅ GPIO (good support)
- ⚠️ EMMC/SD (basic)
- ⚠️ Mailbox (limited property tags)
- ❌ WiFi/Bluetooth
- ❌ USB
- ❌ HDMI

#### Use Cases
- ARMv8-A 64-bit development
- AArch64 instruction set testing
- Lower memory footprint testing
- Compact embedded systems

---

### 4. Raspberry Pi 3B (BCM2837) ✅

**Machine ID:** `raspi3b`
**Used in this bootloader project**

#### Hardware Specifications
- **CPU:** ARM Cortex-A53 (ARMv8-A 64-bit)
- **Cores:** 4 cores (quad-core)
- **Clock Speed:** 1.2 GHz
- **RAM:** 1 GB
- **GPU:** VideoCore IV
- **Peripheral Base:** 0x3F000000

#### QEMU Support
```bash
# Boot with AArch64 emulator (64-bit kernel)
qemu-system-aarch64 -M raspi3b -kernel kernel8.img -nographic

# With serial output
qemu-system-aarch64 -M raspi3b -kernel kernel8.img -nographic -serial mon:stdio

# With serial to file
qemu-system-aarch64 -M raspi3b -kernel kernel8.img -nographic -serial file:output.txt

# Multi-core boot
qemu-system-aarch64 -M raspi3b -smp 4 -kernel kernel8.img -nographic

# With custom memory size
qemu-system-aarch64 -M raspi3b -m 1G -kernel kernel8.img -nographic
```

#### Emulated Peripherals
- ✅ UART (PL011 at 0x3F201000) - **Full support**
- ✅ System Timer - **Full support**
- ✅ GPIO - **Good support**
- ✅ EMMC/SD - **Basic support** (limited in QEMU)
- ✅ Mailbox - **Limited support** (basic property tags)
- ⚠️ Interrupt Controller (GIC-400)
- ❌ WiFi/Bluetooth
- ❌ USB
- ❌ HDMI
- ❌ Ethernet

#### Memory Map (BCM2837)
```
0x00000000 - 0x3EFFFFFF  SDRAM (1 GB)
0x3F000000 - 0x3FFFFFFF  Peripherals
  0x3F003000 - System Timer
  0x3F00B000 - Mailbox
  0x3F100000 - Power Management
  0x3F200000 - GPIO
  0x3F201000 - UART0 (PL011)
  0x3F215000 - Mini UART
  0x3F300000 - EMMC/SD Card
0x40000000 - 0xFFFFFFFF  Local peripherals, ARM, GPU
```

#### Bootloader Project Configuration
```c
// UART base address for QEMU raspi3b
#define UART_BASE 0x3F201000

// Timer base
#define TIMER_BASE 0x3F003000

// GPIO base
#define GPIO_BASE 0x3F200000

// Mailbox base
#define MBOX_BASE 0x3F00B000

// EMMC base
#define EMMC_BASE 0x3F300000
```

#### Use Cases
- **Bare-metal bootloader development** ✅ (this project!)
- 64-bit ARM kernel development
- Multi-core ARM development
- UART-based debugging
- Timer and GPIO testing
- Educational OS development

#### Known Limitations in QEMU
1. **EMMC/SD Card:**
   - No actual SD card image support in raspi3b model
   - SD initialization commands timeout or fail
   - This project implements SD driver that gracefully handles QEMU's limitations

2. **Mailbox:**
   - Limited VideoCore firmware emulation
   - Many property tags return timeouts
   - Basic queries may work but don't return real hardware info

3. **GPIO:**
   - No actual hardware state
   - Register reads/writes work but don't control physical pins
   - Good for testing logic, not for hardware interaction

4. **Networking:**
   - No Ethernet emulation (Pi 3B has Ethernet via USB)
   - No WiFi/Bluetooth support

5. **USB:**
   - No USB controller emulation
   - Cannot attach USB devices

#### Best Practices for QEMU Development
1. Use reduced timeouts for SD/EMMC operations
2. Implement graceful fallback when peripherals timeout
3. Test on real hardware for production deployment
4. Use UART for all debugging output
5. Don't rely on mailbox for critical functionality

---

### 5. Raspberry Pi 4B (BCM2711)

**Machine ID:** `raspi4b`

#### Hardware Specifications
- **CPU:** ARM Cortex-A72 (ARMv8-A 64-bit)
- **Cores:** 4 cores (quad-core)
- **Clock Speed:** 1.5 GHz
- **RAM:** 1 GB / 2 GB / 4 GB / 8 GB variants
- **GPU:** VideoCore VI
- **Peripheral Base:** 0xFE000000 (different from Pi 3!)

#### QEMU Support
```bash
# Boot with AArch64 emulator (64-bit kernel)
qemu-system-aarch64 -M raspi4b -kernel kernel8.img -nographic

# With 4GB RAM variant
qemu-system-aarch64 -M raspi4b -m 4G -kernel kernel8.img -nographic

# Multi-core boot
qemu-system-aarch64 -M raspi4b -smp 4 -kernel kernel8.img -nographic
```

#### Emulated Peripherals
- ✅ UART (PL011 at 0xFE201000)
- ✅ System Timer
- ✅ GPIO
- ⚠️ EMMC/SD (basic)
- ⚠️ Mailbox (limited)
- ⚠️ GENET Ethernet (very limited)
- ❌ PCIe
- ❌ USB 3.0
- ❌ Dual HDMI
- ❌ WiFi/Bluetooth

#### Key Differences from Pi 3B
- **Peripheral Base:** 0xFE000000 (vs 0x3F000000)
- **UART Address:** 0xFE201000 (vs 0x3F201000)
- **More powerful CPU:** Cortex-A72 vs Cortex-A53
- **More RAM options:** Up to 8 GB
- **Better QEMU emulation:** Newer model, better support

#### Use Cases
- Latest ARM development
- High-performance embedded systems
- Large memory applications
- Modern bootloader development

---

## Peripheral Base Address Summary

| Model | SoC | Peripheral Base | UART0 Address | Notes |
|-------|-----|-----------------|---------------|-------|
| Pi 0, 1A+ | BCM2835 | 0x20000000 | 0x20201000 | Legacy base |
| Pi 2B | BCM2836 | 0x3F000000 | 0x3F201000 | Standard base |
| Pi 3A+, 3B | BCM2837/B0 | 0x3F000000 | 0x3F201000 | Same as Pi 2B ✅ |
| Pi 4B | BCM2711 | 0xFE000000 | 0xFE201000 | New base! |

**Important:** Always detect the hardware model and set peripheral addresses accordingly!

---

## QEMU Command Reference

### Basic Boot Commands

```bash
# Raspberry Pi 3B (this project)
qemu-system-aarch64 -M raspi3b -kernel bootloader.bin -nographic

# With monitor access (Ctrl-A C to toggle)
qemu-system-aarch64 -M raspi3b -kernel bootloader.bin -nographic -serial mon:stdio

# With serial output to file
qemu-system-aarch64 -M raspi3b -kernel bootloader.bin -nographic -serial file:output.txt

# With custom memory
qemu-system-aarch64 -M raspi3b -m 1G -kernel bootloader.bin -nographic

# Multi-core boot (4 cores)
qemu-system-aarch64 -M raspi3b -smp 4 -kernel bootloader.bin -nographic
```

### Advanced Options

```bash
# With SD card image (limited support)
qemu-system-aarch64 -M raspi3b -kernel bootloader.bin -sd sd.img -nographic

# With device tree blob
qemu-system-aarch64 -M raspi3b -kernel bootloader.bin -dtb bcm2710-rpi-3-b.dtb -nographic

# With append arguments
qemu-system-aarch64 -M raspi3b -kernel bootloader.bin -append "console=ttyAMA0" -nographic

# Exit QEMU: Ctrl-A X
# Access monitor: Ctrl-A C (when using -serial mon:stdio)
```

### Debugging Options

```bash
# Enable QEMU logging
qemu-system-aarch64 -M raspi3b -kernel bootloader.bin -nographic -d guest_errors

# Enable GDB server (port 1234)
qemu-system-aarch64 -M raspi3b -kernel bootloader.bin -nographic -s -S

# Then connect with:
# aarch64-elf-gdb bootloader.elf
# (gdb) target remote localhost:1234
# (gdb) continue
```

### Information Commands

```bash
# List all machines
qemu-system-aarch64 -M help | grep raspi

# List all CPUs
qemu-system-aarch64 -cpu help

# Show version
qemu-system-aarch64 --version

# Show default machine info
qemu-system-aarch64 -M raspi3b,help
```

---

## Makefile Integration

### Example Makefile Target

```makefile
# QEMU test target
.PHONY: qemu-test
qemu-test: bootloader.bin
	@echo "Running bootloader in QEMU (raspi3b)..."
	qemu-system-aarch64 -M raspi3b -kernel bootloader.bin \
		-nographic -serial mon:stdio

# Background test with output capture
.PHONY: qemu-capture
qemu-capture: bootloader.bin
	@rm -f uart_output.txt
	qemu-system-aarch64 -M raspi3b -kernel bootloader.bin \
		-nographic -serial file:uart_output.txt &
	@sleep 2
	@pkill -9 qemu-system-aarch64 || true
	@cat uart_output.txt

# Multi-core test
.PHONY: qemu-smp
qemu-smp: bootloader.bin
	qemu-system-aarch64 -M raspi3b -smp 4 -kernel bootloader.bin \
		-nographic -serial mon:stdio
```

---

## Real Hardware vs QEMU

### What Works in QEMU

| Feature | QEMU | Real Hardware | Notes |
|---------|------|---------------|-------|
| **CPU execution** | ✅ Full | ✅ Full | Accurate ARM execution |
| **UART output** | ✅ Full | ✅ Full | Perfect for debugging |
| **Timer** | ✅ Good | ✅ Full | Timing may differ |
| **GPIO registers** | ✅ Read/Write | ✅ Full | No physical state |
| **Mailbox** | ⚠️ Limited | ✅ Full | Timeouts common |
| **EMMC/SD** | ⚠️ Very Limited | ✅ Full | Driver loads but no data |
| **Interrupts** | ⚠️ Basic | ✅ Full | Limited implementation |
| **USB** | ❌ None | ✅ Full | Not emulated |
| **Ethernet** | ❌ None (Pi3) | ✅ Full | Not emulated |
| **WiFi/BT** | ❌ None | ✅ Full | Not emulated |
| **HDMI** | ❌ None | ✅ Full | Not emulated |
| **Camera** | ❌ None | ✅ Full | Not emulated |

### Development Workflow

```
┌─────────────────┐
│ Develop Code    │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│ Test in QEMU    │◄─── Quick iteration
└────────┬────────┘     Fast boot
         │              Easy debugging
         ▼
┌─────────────────┐
│ Fix QEMU Issues │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│ Test on Real HW │◄─── Final validation
└────────┬────────┘     Full peripherals
         │              Production env
         ▼
┌─────────────────┐
│ Deploy          │
└─────────────────┘
```

**Best Practice:** Develop and debug in QEMU, validate on real hardware.

---

## Troubleshooting

### Common Issues

#### 1. QEMU Hangs During Boot

**Problem:** Bootloader appears to freeze in QEMU.

**Likely Causes:**
- Waiting for SD/EMMC with long timeouts
- Waiting for mailbox response
- Infinite loop with no WFI instruction

**Solutions:**
```c
// Reduce SD initialization timeout
#define SD_TIMEOUT 100  // Not 1000000

// Add WFI in idle loops
while (1) {
    __asm__ volatile("wfi");
}

// Add timeout checks for mailbox
uint32_t timeout = 10000;
while (!(mailbox_read() & 0x80000000) && timeout--) {
    // Wait
}
```

#### 2. No Serial Output

**Problem:** No output appears in QEMU terminal.

**Solutions:**
```bash
# Ensure you're using -nographic
qemu-system-aarch64 -M raspi3b -kernel bootloader.bin -nographic

# Try explicit serial output
qemu-system-aarch64 -M raspi3b -kernel bootloader.bin \
    -nographic -serial mon:stdio

# Check UART is initialized and using correct address
# For raspi3b: 0x3F201000
```

#### 3. Wrong Peripheral Addresses

**Problem:** Peripherals not responding.

**Solution:** Use correct peripheral base for model:
```c
#if defined(RASPI4)
    #define PERIPHERAL_BASE 0xFE000000
#elif defined(RASPI3) || defined(RASPI2)
    #define PERIPHERAL_BASE 0x3F000000
#else
    #define PERIPHERAL_BASE 0x20000000  // Pi 0, 1
#endif

#define UART0_BASE (PERIPHERAL_BASE + 0x201000)
```

#### 4. SD Card Not Working

**Problem:** SD initialization fails.

**Expected:** QEMU's raspi3b has very limited EMMC emulation.

**Solutions:**
```c
// Detect QEMU vs real hardware
int sd_status = sd_init();
if (sd_status != 0) {
    uart_puts("SD init failed (expected in QEMU)\n");
    // Continue without SD
}
```

---

## Model Selection Guide

### For This Bootloader Project

**Recommended:** Raspberry Pi 3B (`raspi3b`) ✅

**Reasons:**
- Good QEMU support
- 64-bit ARM (AArch64)
- Standard peripheral base (0x3F000000)
- 1GB RAM (enough for development)
- Well-documented BCM2837
- Easy migration to Pi 3A+
- Similar to Pi 2B (same peripheral base)

### For Other Projects

| Project Type | Recommended Model | Reason |
|--------------|-------------------|--------|
| **Legacy ARM** | Pi Zero / 1A+ | ARMv6 architecture |
| **32-bit development** | Pi 2B | Multi-core ARMv7 |
| **Modern 64-bit** | Pi 3B / 3A+ | Best QEMU support |
| **Latest features** | Pi 4B | Most powerful, newest |
| **Memory-limited** | Pi 3A+ | 512MB testing |
| **SMP testing** | Pi 2B / 3B / 4B | Multi-core support |

---

## Quick Reference Card

### Machine IDs
```
raspi0    - Pi Zero (BCM2835, ARM1176)
raspi1ap  - Pi 1 A+ (BCM2835, ARM1176)
raspi2b   - Pi 2B (BCM2836, Cortex-A7)
raspi3ap  - Pi 3 A+ (BCM2837B0, Cortex-A53)
raspi3b   - Pi 3B (BCM2837, Cortex-A53) ✅
raspi4b   - Pi 4B (BCM2711, Cortex-A72)
```

### Peripheral Bases
```
0x20000000 - Pi 0, 1
0x3F000000 - Pi 2, 3 ✅
0xFE000000 - Pi 4
```

### UART Addresses
```
0x20201000 - Pi 0, 1
0x3F201000 - Pi 2, 3 ✅
0xFE201000 - Pi 4
```

### Boot Commands
```bash
# Pi 3B (64-bit)
qemu-system-aarch64 -M raspi3b -kernel kernel8.img -nographic

# With serial
qemu-system-aarch64 -M raspi3b -kernel kernel8.img \
    -nographic -serial mon:stdio

# Exit: Ctrl-A X
```

---

## References

### Official Documentation
- [QEMU Raspberry Pi Emulation](https://www.qemu.org/docs/master/system/arm/raspi.html)
- [Raspberry Pi Documentation](https://www.raspberrypi.com/documentation/)
- [BCM2835 Peripherals](https://www.raspberrypi.org/app/uploads/2012/02/BCM2835-ARM-Peripherals.pdf)

### This Project
- See `README.md` for bootloader details
- See `BUILD_SUMMARY.md` for implementation notes
- See `bootloader/` directory for source code

---

**Last Updated:** October 18, 2025
**QEMU Version:** 10.1.1
**Bootloader:** ARM64 Bare-Metal Bootloader for Raspberry Pi 3B
