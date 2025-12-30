# Action Plan: Make All 7 QEMU Platforms Work
## From 2/7 Success to 7/7 Success

**Current Status**: 2/7 platforms work (raspi3ap, raspi3b)
**Goal**: Make all 7 platforms boot successfully
**Estimated Time**: 4-6 hours of focused work

---

## Current Test Results Summary

| Platform | Status | Issue | Fix Complexity |
|----------|--------|-------|----------------|
| raspi3ap | ✅ **WORKS** | None | N/A |
| raspi3b | ✅ **WORKS** | None | N/A |
| raspi2b | ❌ Fails | Needs firmware | EASY (create SD image) |
| raspi0 | ❌ Fails | Needs firmware + address fix | MEDIUM (firmware + code) |
| raspi1ap | ❌ Fails | Needs firmware + address fix | MEDIUM (firmware + code) |
| raspi4b | ❌ Fails | Needs firmware + address fix | MEDIUM (firmware + code) |
| virt | ❌ Fails | Address mismatch | MEDIUM (code changes) |

---

## Fix Strategy

### Phase 1: Easy Wins (30 minutes)

**Target**: raspi2b

**Why Easy**: Uses same addresses as raspi3b (0x3F...), just needs firmware

**Steps**:
1. Create SD card image
2. Add firmware files
3. Test

**Expected**: raspi2b will work → 3/7 success

---

### Phase 2: Add Hardware Abstraction (2 hours)

**Target**: All platforms

**Current Problem**:
```c
// uart.c - HARDCODED
#define UART_BASE 0x3F201000  // Only works for BCM2837
```

**Solution**: Runtime address detection

**Implementation**:

1. **Add to Makefile**:
```makefile
SRC_C = main.c uart.c timer.c gpio.c memory.c mailbox.c sd.c hardware.c hal.c
```

2. **Create hardware.c** (simplified):
```c
#include "hardware.h"

typedef enum {
    PLATFORM_UNKNOWN,
    PLATFORM_VIRT,
    PLATFORM_BCM2835,  // Pi 0, 1
    PLATFORM_BCM2837,  // Pi 2, 3
    PLATFORM_BCM2711   // Pi 4
} platform_t;

static platform_t current_platform = PLATFORM_UNKNOWN;

void hardware_detect_platform(void) {
    // Try mailbox (Raspberry Pi hardware)
    if (mailbox_probe() == 0) {
        uint32_t revision = mailbox_get_revision();

        // Decode revision to determine platform
        // (simplified - real code needs full revision table)
        if (revision & 0x800000) {
            // New-style revision
            uint32_t type = (revision >> 4) & 0xFF;
            if (type >= 0x11 && type <= 0x14) {
                current_platform = PLATFORM_BCM2711; // Pi 4
            } else if (type >= 0x08 && type <= 0x0E) {
                current_platform = PLATFORM_BCM2837; // Pi 2/3
            } else {
                current_platform = PLATFORM_BCM2835; // Pi 0/1
            }
        }
    } else {
        // No mailbox = QEMU virt
        current_platform = PLATFORM_VIRT;
    }
}

uintptr_t get_uart_base(void) {
    switch (current_platform) {
        case PLATFORM_VIRT:    return 0x09000000;
        case PLATFORM_BCM2835: return 0x20201000;
        case PLATFORM_BCM2837: return 0x3F201000;
        case PLATFORM_BCM2711: return 0xFE201000;
        default:               return 0x3F201000; // Safe fallback
    }
}

// Similar functions for GPIO, Timer, etc.
```

3. **Update uart.c**:
```c
#include "hardware.h"

// Remove hardcoded address
// #define UART_BASE 0x3F201000

void uart_init(void) {
    uintptr_t uart_base = get_uart_base();  // Runtime detection!

    // Use uart_base instead of UART_BASE
    mmio_write(uart_base + 0x30, 0);  // CR
    mmio_write(uart_base + 0x24, 26); // IBRD
    // ... rest of init
}
```

4. **Call detection in main.c**:
```c
void main(void) {
    hardware_detect_platform();  // First thing!

    uart_init();  // Now uses correct address
    // ... rest of boot
}
```

**Expected**: virt, raspi0, raspi1ap, raspi4b will now work → 7/7 success (with firmware for raspi*)

---

### Phase 3: Create Firmware Images (1 hour)

**Target**: raspi0, raspi1ap, raspi2b, raspi4b

**Script**: `create_sd_images.sh`

```bash
#!/bin/bash

create_sd_image() {
    local MODEL=$1
    local START_ELF=$2
    local FIXUP_DAT=$3
    local IMG="sdcard_${MODEL}.img"

    echo "Creating $IMG..."

    # Create 64MB image
    dd if=/dev/zero of="$IMG" bs=1M count=64 2>/dev/null

    # Format as FAT32
    mkfs.vfat "$IMG" >/dev/null 2>&1

    # Mount (macOS method)
    hdiutil attach "$IMG" -mountpoint /tmp/sdmount 2>/dev/null || {
        # Linux method
        mkdir -p /tmp/sdmount
        mount -o loop "$IMG" /tmp/sdmount
    }

    # Copy firmware
    cp /tmp/rpi_firmware/bootcode.bin /tmp/sdmount/
    cp "/tmp/rpi_firmware/$START_ELF" /tmp/sdmount/
    cp "/tmp/rpi_firmware/$FIXUP_DAT" /tmp/sdmount/

    # Copy bootloader
    cp bootloader.bin /tmp/sdmount/kernel8.img

    # Create config.txt
    cat > /tmp/sdmount/config.txt <<EOF
arm_64bit=1
enable_uart=1
kernel=kernel8.img
gpu_mem=16
EOF

    # Unmount
    hdiutil detach /tmp/sdmount 2>/dev/null || umount /tmp/sdmount

    echo "✓ Created $IMG"
}

# Create images for each platform
create_sd_image "raspi0" "start.elf" "fixup.dat"
create_sd_image "raspi1ap" "start.elf" "fixup.dat"
create_sd_image "raspi2b" "start.elf" "fixup.dat"
create_sd_image "raspi4b" "start4.elf" "fixup4.dat"

echo ""
echo "All SD card images created!"
echo "Test with:"
echo "  qemu-system-aarch64 -M raspi2b -sd sdcard_raspi2b.img -nographic"
```

---

## Detailed Step-by-Step Plan

### Step 1: Fix raspi2b (Quick Win)

**Time**: 30 minutes

```bash
# 1. Create SD image script
cat > create_sd_raspi2b.sh <<'EOF'
#!/bin/bash
dd if=/dev/zero of=sdcard_raspi2b.img bs=1M count=64
mkfs.vfat sdcard_raspi2b.img
hdiutil attach sdcard_raspi2b.img -mountpoint /tmp/sdmount
cp /tmp/rpi_firmware/bootcode.bin /tmp/sdmount/
cp /tmp/rpi_firmware/start.elf /tmp/sdmount/
cp /tmp/rpi_firmware/fixup.dat /tmp/sdmount/
cp bootloader.bin /tmp/sdmount/kernel8.img
cat > /tmp/sdmount/config.txt <<CONF
arm_64bit=1
enable_uart=1
kernel=kernel8.img
CONF
hdiutil detach /tmp/sdmount
EOF

chmod +x create_sd_raspi2b.sh
./create_sd_raspi2b.sh

# 2. Test
qemu-system-aarch64 -M raspi2b -sd sdcard_raspi2b.img -nographic

# Expected: Full boot output!
```

---

### Step 2: Add Hardware Detection (Core Fix)

**Time**: 2 hours

**2a. Create hardware.c** (30 min)

Create `src/hardware.c` with platform detection (see Phase 2 above)

**2b. Create hardware.h** (15 min)

```c
#ifndef HARDWARE_H
#define HARDWARE_H

#include <stdint.h>

typedef enum {
    PLATFORM_UNKNOWN,
    PLATFORM_VIRT,
    PLATFORM_BCM2835,
    PLATFORM_BCM2837,
    PLATFORM_BCM2711
} platform_t;

void hardware_detect_platform(void);
platform_t hardware_get_platform(void);

uintptr_t get_uart_base(void);
uintptr_t get_gpio_base(void);
uintptr_t get_timer_base(void);
uintptr_t get_mailbox_base(void);

#endif
```

**2c. Update Makefile** (5 min)

```makefile
SRC_C = main.c uart.c timer.c gpio.c memory.c mailbox.c sd.c hardware.c
```

**2d. Update uart.c** (20 min)

Replace all `UART_BASE` with `get_uart_base()` calls

**2e. Update timer.c** (20 min)

Replace all `TIMER_BASE` with `get_timer_base()` calls

**2f. Update gpio.c** (20 min)

Replace all `GPIO_BASE` with `get_gpio_base()` calls

**2g. Update mailbox.c** (20 min)

Replace all `MAILBOX_BASE` with `get_mailbox_base()` calls

**2h. Update main.c** (10 min)

Add `hardware_detect_platform()` as first call in `main()`

**2i. Rebuild and test** (10 min)

```bash
make clean
make

# Test virt (should now work!)
qemu-system-aarch64 -M virt -cpu cortex-a72 -m 1G \
  -kernel bootloader.bin -nographic

# Expected: Full boot output with correct UART!
```

---

### Step 3: Create All SD Images

**Time**: 30 minutes

Run the `create_sd_images.sh` script from Phase 3

---

### Step 4: Test All Platforms

**Time**: 1 hour

```bash
# Test each platform
qemu-system-aarch64 -M virt -kernel bootloader.bin -nographic
qemu-system-aarch64 -M raspi0 -sd sdcard_raspi0.img -nographic
qemu-system-aarch64 -M raspi1ap -sd sdcard_raspi1ap.img -nographic
qemu-system-aarch64 -M raspi2b -sd sdcard_raspi2b.img -nographic
qemu-system-aarch64 -M raspi3ap -kernel bootloader.bin -nographic
qemu-system-aarch64 -M raspi3b -kernel bootloader.bin -nographic
qemu-system-aarch64 -M raspi4b -sd sdcard_raspi4b.img -nographic
```

**Expected**: All 7 platforms boot successfully!

---

## Potential Issues & Solutions

### Issue 1: mailbox_probe() doesn't exist

**Solution**: Add simple probe function:

```c
int mailbox_probe(void) {
    // Try to read mailbox status register
    // If it works, we have a mailbox (Raspberry Pi)
    // If it fails/hangs, no mailbox (virt)

    volatile uint32_t *status = (volatile uint32_t*)0x3F00B898;

    // Set timeout
    for (int i = 0; i < 1000; i++) {
        uint32_t val = *status;
        if (val != 0xFFFFFFFF && val != 0x00000000) {
            return 0; // Success - mailbox exists
        }
    }

    return -1; // Timeout - no mailbox
}
```

### Issue 2: SD card image creation fails on macOS

**Solution**: Use hdiutil instead of mount:

```bash
# macOS version
hdiutil attach image.img -mountpoint /tmp/sdmount
# ... copy files ...
hdiutil detach /tmp/sdmount
```

### Issue 3: Some platforms still don't boot with firmware

**Solution**: Check QEMU debug logs, may need:
- Different firmware versions
- Additional config.txt settings
- GDB workaround for testing

---

## Success Metrics

### After Step 1 (raspi2b firmware)
- 3/7 platforms working (43%)

### After Step 2 (hardware abstraction)
- 4/7 platforms working (57%) - virt now works
- Potentially 5/7 if direct kernel boot works for raspi0/1ap

### After Steps 3-4 (all firmware + testing)
- 7/7 platforms working (100%) ✅

---

## Timeline

**Optimistic**: 3-4 hours total
- Step 1: 30 min
- Step 2: 2 hours
- Step 3: 30 min
- Step 4: 30 min

**Realistic**: 4-6 hours total
- Includes debugging time
- Handling unexpected issues
- Testing and verification

**If issues**: 6-8 hours total
- Complex platform-specific bugs
- Firmware compatibility problems
- QEMU quirks

---

## Next Session Plan

**Session Goal**: Get to 4/7 or 5/7 working

**Priority Order**:
1. ✅ Create raspi2b SD image (30 min) - Easy win
2. ✅ Implement hardware.c minimal version (1 hour) - Core fix
3. ✅ Test virt with new code (15 min) - Verify it works
4. ✅ Update UART/GPIO/Timer with get_*_base() (1 hour)
5. ✅ Full rebuild and test (30 min)

**Deliverable**: Working bootloader on virt + all raspi2/3 platforms

---

## Long-term (Week 2)

1. Create comprehensive hardware detection
2. Support all SoC variants
3. Test on real hardware
4. Add multi-core support
5. Optimize for each platform

---

**Current State**: 2/7 success (raspi3ap, raspi3b)
**Next Milestone**: 4/7 success (add virt, raspi2b)
**Final Goal**: 7/7 success (all QEMU platforms)

**The path is clear. Let's make it happen!**
