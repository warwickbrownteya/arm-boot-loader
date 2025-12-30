# QEMU Emulation Targets - Comprehensive Analysis
## Virtual Testing Matrix for ARM64 Bootloader

**Date**: 2025-10-19
**Purpose**: Document requirements for testing bootloader across all QEMU ARM targets
**Status**: Planning virtual test campaign

---

## Executive Summary

**Goal**: Test bootloader on all 7 QEMU ARM emulation targets before physical hardware deployment

**Target Platforms**:
- 6 Raspberry Pi emulation targets (raspi0, raspi1ap, raspi2b, raspi3ap, raspi3b, raspi4b)
- 1 Generic ARM virtual machine (virt)

**Current Status**: Only tested on `virt` (working)

---

## I. QEMU Machine Specifications

### 1. virt - QEMU ARM Virtual Machine

**QEMU Machine**: `virt` (alias for virt-10.1)

**Architecture**: Generic ARMv8-A
**CPU**: Configurable (default: cortex-a57)
**Memory**: Configurable (default: 128MB)
**Peripherals**:
- PL011 UART at 0x09000000
- PL031 RTC
- PL061 GPIO
- Generic interrupt controller (GIC-400)
- VirtIO devices

**Boot Method**: **Direct kernel load** (-kernel flag)
**GPU Firmware**: **NOT REQUIRED**

**Status**: ✅ **WORKS** - Bootloader boots successfully

**Command**:
```bash
qemu-system-aarch64 -M virt -cpu cortex-a72 -m 1G \
  -kernel bootloader.bin \
  -serial stdio -nographic \
  -d guest_errors,cpu_reset -D qemu_virt.log
```

**Peripheral Addresses (virt)**:
```
UART:   0x09000000  (PL011)
GIC:    0x08000000  (distributor)
        0x08010000  (CPU interface)
Timer:  System registers (not MMIO)
GPIO:   0x09030000  (PL061)
```

**Requirements for Bootloader**:
- Detect virt machine (no mailbox available)
- Use virt-specific peripheral addresses
- Handle direct kernel boot (CPU starts at entry point)

---

### 2. raspi0 - Raspberry Pi Zero

**QEMU Machine**: `raspi0`

**Architecture**: ARMv6 (32-bit ARM1176)
**SoC**: BCM2835
**CPU**: ARM1176JZF-S (single core)
**Memory**: 512MB
**Peripherals**:
- PL011 UART at 0x20201000
- BCM2835 GPIO at 0x20200000
- System Timer at 0x20003000
- Mailbox at 0x2000B880

**Boot Method**: **Requires GPU firmware**
**GPU Firmware Files**:
- bootcode.bin
- start.elf
- fixup.dat

**Status**: 🔬 **UNTESTED**

**Command**:
```bash
# Option 1: With SD card image containing firmware
qemu-system-aarch64 -M raspi0 -m 512M \
  -sd sdcard.img \
  -serial stdio -nographic \
  -d guest_errors,cpu_reset -D qemu_raspi0.log

# Option 2: With GDB (manually set PC)
qemu-system-aarch64 -M raspi0 -m 512M \
  -kernel bootloader.bin \
  -serial stdio -nographic \
  -s -S  # Wait for GDB
# Then: gdb> target remote :1234; set $pc=0x8000; continue
```

**Peripheral Addresses (BCM2835)**:
```
UART:     0x20201000
GPIO:     0x20200000
Timer:    0x20003000
Mailbox:  0x2000B880
EMMC:     0x20300000
```

**Requirements for Bootloader**:
- Support 32-bit ARM (not 64-bit)
- Use BCM2835 peripheral addresses
- Handle lack of direct boot (need firmware or GDB hack)

**Note**: Pi Zero is ARMv6 32-bit, but QEMU raspi0 can run in 64-bit mode with proper firmware

---

### 3. raspi1ap - Raspberry Pi A+

**QEMU Machine**: `raspi1ap`

**Architecture**: ARMv6 (32-bit ARM1176)
**SoC**: BCM2835
**CPU**: ARM1176JZF-S (single core)
**Memory**: 512MB
**Peripherals**: Same as raspi0

**Boot Method**: **Requires GPU firmware**
**GPU Firmware Files**:
- bootcode.bin
- start.elf
- fixup.dat

**Status**: 🔬 **UNTESTED**

**Command**: Same as raspi0

**Peripheral Addresses**: Same as BCM2835 (raspi0)

**Requirements**: Same as raspi0

---

### 4. raspi2b - Raspberry Pi 2B

**QEMU Machine**: `raspi2b`

**Architecture**: ARMv7 / ARMv8
**SoC**: BCM2836 (quad-core Cortex-A7) or BCM2837 (quad-core Cortex-A53)
**CPU**: 4x Cortex-A7 or 4x Cortex-A53
**Memory**: 1GB
**Peripherals**:
- PL011 UART at 0x3F201000
- BCM2836 GPIO at 0x3F200000
- System Timer at 0x3F003000
- Mailbox at 0x3F00B880

**Boot Method**: **Requires GPU firmware**
**GPU Firmware Files**:
- bootcode.bin
- start.elf
- fixup.dat

**Status**: 🔬 **UNTESTED**

**Command**:
```bash
qemu-system-aarch64 -M raspi2b -m 1G \
  -sd sdcard.img \
  -serial stdio -nographic \
  -d guest_errors,cpu_reset -D qemu_raspi2b.log
```

**Peripheral Addresses (BCM2836/2837)**:
```
UART:     0x3F201000  (Note: different from raspi0!)
GPIO:     0x3F200000
Timer:    0x3F003000
Mailbox:  0x3F00B880
EMMC:     0x3F300000
```

**Requirements for Bootloader**:
- Support BCM2836/2837 addresses
- Handle multi-core (4 CPUs)
- Detect Pi 2B vs Pi 3B (different SoCs)

---

### 5. raspi3ap - Raspberry Pi 3A+

**QEMU Machine**: `raspi3ap`

**Architecture**: ARMv8 (64-bit)
**SoC**: BCM2837B0
**CPU**: 4x Cortex-A53
**Memory**: 512MB
**Peripherals**: Same as raspi2b (BCM2837)

**Boot Method**: **Requires GPU firmware**
**GPU Firmware Files**:
- bootcode.bin
- start.elf
- fixup.dat

**Status**: 🔬 **UNTESTED**

**Command**:
```bash
qemu-system-aarch64 -M raspi3ap -m 512M \
  -sd sdcard.img \
  -serial stdio -nographic \
  -d guest_errors,cpu_reset -D qemu_raspi3ap.log
```

**Peripheral Addresses**: Same as BCM2837 (raspi2b)

**Requirements**: Same as raspi2b, but with 512MB RAM

---

### 6. raspi3b - Raspberry Pi 3B ✅

**QEMU Machine**: `raspi3b`

**Architecture**: ARMv8 (64-bit)
**SoC**: BCM2837
**CPU**: 4x Cortex-A53
**Memory**: 1GB
**Peripherals**: Same as raspi2b

**Boot Method**: **Requires GPU firmware**
**GPU Firmware Files**:
- bootcode.bin
- start.elf
- fixup.dat

**Status**: ⚠️ **PARTIAL** - Loads binary but CPU doesn't start (expected without firmware)

**Command**:
```bash
# Current bootloader (BCM2837 hardcoded addresses)
qemu-system-aarch64 -M raspi3b \
  -kernel bootloader.bin \
  -serial stdio -nographic \
  -d guest_errors,cpu_reset -D qemu_raspi3b.log

# Expected result: CPU halts at 0x0, no output (need firmware)
```

**Peripheral Addresses (BCM2837)**:
```
UART:     0x3F201000  ✅ Matches current bootloader
GPIO:     0x3F200000  ✅ Matches current bootloader
Timer:    0x3F003000  ✅ Matches current bootloader
Mailbox:  0x3F00B880  ✅ Matches current bootloader
```

**Requirements**: Current bootloader is ALREADY configured for raspi3b addresses!

---

### 7. raspi4b - Raspberry Pi 4B

**QEMU Machine**: `raspi4b`

**Architecture**: ARMv8 (64-bit)
**SoC**: BCM2711
**CPU**: 4x Cortex-A72
**Memory**: 1GB, 2GB, 4GB, or 8GB (QEMU: configurable)
**Peripherals**:
- PL011 UART at **0xFE201000** ⚠️ DIFFERENT!
- BCM2711 GPIO at **0xFE200000** ⚠️ DIFFERENT!
- System Timer at **0xFE003000** ⚠️ DIFFERENT!
- Mailbox at **0xFE00B880** ⚠️ DIFFERENT!

**Boot Method**: **Requires GPU firmware**
**GPU Firmware Files**:
- bootcode.bin
- start4.elf (**different from Pi 3**)
- fixup4.dat (**different from Pi 3**)

**Status**: 🔬 **UNTESTED** in QEMU, ❌ **FAILED** on real hardware

**Command**:
```bash
qemu-system-aarch64 -M raspi4b -m 4G \
  -sd sdcard.img \
  -serial stdio -nographic \
  -d guest_errors,cpu_reset -D qemu_raspi4b.log
```

**Peripheral Addresses (BCM2711)**:
```
UART:     0xFE201000  ❌ CURRENT BOOTLOADER WRONG (uses 0x3F201000)
GPIO:     0xFE200000  ❌ CURRENT BOOTLOADER WRONG
Timer:    0xFE003000  ❌ CURRENT BOOTLOADER WRONG
Mailbox:  0xFE00B880  ❌ CURRENT BOOTLOADER WRONG
```

**Requirements for Bootloader**:
- **MUST** use BCM2711 addresses (0xFE... not 0x3F...)
- Detect Pi 4 via mailbox or hardware detection
- Use start4.elf instead of start.elf

**This is why real Pi 4B failed!**

---

## II. Peripheral Address Summary

| Platform | Base Offset | UART | GPIO | Timer | Mailbox |
|----------|-------------|------|------|-------|---------|
| virt | N/A | 0x09000000 | 0x09030000 | (sysreg) | N/A |
| raspi0/1ap | 0x20000000 | 0x20201000 | 0x20200000 | 0x20003000 | 0x2000B880 |
| raspi2b/3ap/3b | 0x3F000000 | 0x3F201000 | 0x3F200000 | 0x3F003000 | 0x3F00B880 |
| raspi4b | 0xFE000000 | 0xFE201000 | 0xFE200000 | 0xFE003000 | 0xFE00B880 |

**Pattern**:
- BCM2835: Base 0x20000000
- BCM2837: Base 0x3F000000 (Pi 2/3)
- BCM2711: Base 0xFE000000 (Pi 4)
- Virt: Custom addresses

**Current Bootloader**: Hardcoded to BCM2837 (0x3F...)
**Compatibility**: raspi2b, raspi3ap, raspi3b ONLY

---

## III. Boot Method Requirements

### Direct Kernel Boot (virt only)

**How it works**:
1. QEMU loads binary to RAM at entry point (0x80000 or configurable)
2. QEMU sets CPU PC to entry point
3. CPU starts executing immediately
4. No firmware required

**Command**:
```bash
qemu-system-aarch64 -M virt -kernel bootloader.bin
```

**Status**: ✅ **WORKS** with current bootloader

---

### GPU Firmware Boot (All raspi* machines)

**How it works**:
1. QEMU loads SD card image
2. VideoCore GPU firmware loads bootcode.bin
3. GPU executes start.elf
4. GPU initializes ARM CPU
5. GPU loads kernel (our bootloader) to 0x80000
6. GPU jumps ARM CPU to 0x80000
7. Our bootloader executes

**Command**:
```bash
qemu-system-aarch64 -M raspi3b -sd sdcard.img
```

**Status**: ⚠️ **REQUIRES SD CARD IMAGE** with firmware files

---

### GDB Workaround (raspi* without firmware)

**How it works**:
1. QEMU loads bootloader to RAM
2. QEMU halts CPU at 0x0 (waiting for firmware)
3. GDB connects and manually sets PC to 0x80000
4. GDB continues execution
5. Bootloader executes (but peripherals may not be initialized)

**Command**:
```bash
# Terminal 1:
qemu-system-aarch64 -M raspi3b -kernel bootloader.bin -s -S

# Terminal 2:
aarch64-elf-gdb bootloader.elf
(gdb) target remote :1234
(gdb) set $pc=0x80000
(gdb) continue
```

**Status**: ⚠️ **HACK** - Works for basic testing, not realistic boot

---

## IV. SD Card Image Requirements

### For raspi0/1ap (BCM2835)

**Firmware Files**:
```
/bootcode.bin       (GPU first stage)
/start.elf          (GPU firmware)
/fixup.dat          (GPU config)
/kernel8.img        (Our bootloader - renamed!)
/config.txt         (Boot configuration)
```

**config.txt**:
```ini
arm_64bit=1
enable_uart=1
kernel=kernel8.img
```

---

### For raspi2b/3ap/3b (BCM2837)

**Firmware Files**: Same as BCM2835

**Note**: BCM2837 can also use start4.elf but start.elf is recommended

---

### For raspi4b (BCM2711)

**Firmware Files**:
```
/bootcode.bin       (GPU first stage)
/start4.elf         (GPU firmware for Pi 4!)
/fixup4.dat         (GPU config for Pi 4!)
/kernel8.img        (Our bootloader)
/config.txt         (Boot configuration)
```

**config.txt**:
```ini
arm_64bit=1
enable_uart=1
kernel=kernel8.img
gpu_mem=16
```

**Important**: Pi 4 requires start4.elf, not start.elf!

---

## V. Creating SD Card Images for QEMU

### Script: create_qemu_sdcard.sh

```bash
#!/bin/bash
# Create QEMU SD card image for Raspberry Pi emulation

PI_MODEL=$1  # raspi0, raspi2b, raspi3b, raspi4b
IMG_NAME="sdcard_${PI_MODEL}.img"

# Create 64MB FAT32 image
dd if=/dev/zero of=$IMG_NAME bs=1M count=64
mkfs.vfat $IMG_NAME

# Mount image
mkdir -p /tmp/sdcard_mount
mount -o loop $IMG_NAME /tmp/sdcard_mount

# Copy firmware files
cp /tmp/rpi_firmware/bootcode.bin /tmp/sdcard_mount/

if [ "$PI_MODEL" = "raspi4b" ]; then
    # Pi 4 needs start4.elf
    cp /tmp/rpi_firmware/start4.elf /tmp/sdcard_mount/
    cp /tmp/rpi_firmware/fixup4.dat /tmp/sdcard_mount/
else
    # Pi 0/1/2/3 use start.elf
    cp /tmp/rpi_firmware/start.elf /tmp/sdcard_mount/
    cp /tmp/rpi_firmware/fixup.dat /tmp/sdcard_mount/
fi

# Copy bootloader as kernel8.img
cp bootloader.bin /tmp/sdcard_mount/kernel8.img

# Create config.txt
cat > /tmp/sdcard_mount/config.txt <<EOF
arm_64bit=1
enable_uart=1
kernel=kernel8.img
gpu_mem=16
EOF

# Unmount
umount /tmp/sdcard_mount

echo "Created $IMG_NAME for $PI_MODEL"
```

---

## VI. Test Matrix

### Compatibility Matrix (Current Bootloader)

| QEMU Machine | Boot Method | Expected Result | Actual Status |
|--------------|-------------|-----------------|---------------|
| virt | Direct kernel | ✅ Should work | ✅ **WORKS** |
| raspi0 | GPU firmware | ❌ Wrong addresses | 🔬 **UNTESTED** |
| raspi1ap | GPU firmware | ❌ Wrong addresses | 🔬 **UNTESTED** |
| raspi2b | GPU firmware | ✅ Should work | 🔬 **UNTESTED** |
| raspi3ap | GPU firmware | ✅ Should work | 🔬 **UNTESTED** |
| raspi3b | GPU firmware | ✅ Should work | ⚠️ **NO FIRMWARE** |
| raspi4b | GPU firmware | ❌ Wrong addresses | 🔬 **UNTESTED** |

**Summary**: Current bootloader works on virt + raspi2b/3ap/3b (if firmware provided)

---

### Required Code Changes

**For raspi0/1ap Support**:
- Add BCM2835 address detection (0x20...)
- Support 32-bit/64-bit hybrid boot

**For raspi4b Support**:
- Add BCM2711 address detection (0xFE...)
- Use start4.elf firmware

**For All Platforms**:
- Implement hardware detection via mailbox
- Use `hardware.c` and `hal.c` (currently not compiled!)

---

## VII. Recommended Testing Sequence

### Phase 1: Verify Current Compatibility (1 hour)

Test platforms that SHOULD work with current code:

```bash
# 1. virt (already working)
qemu-system-aarch64 -M virt -cpu cortex-a72 -m 1G \
  -kernel bootloader.bin -serial stdio -nographic

# 2. raspi3b with GDB hack (test addressing)
qemu-system-aarch64 -M raspi3b -kernel bootloader.bin \
  -serial stdio -nographic -s -S
# Then GDB: set $pc=0x80000

# 3. raspi2b with GDB hack (same addresses as raspi3b)
qemu-system-aarch64 -M raspi2b -kernel bootloader.bin \
  -serial stdio -nographic -s -S
```

**Expected**: virt works, raspi2b/3b show UART output with GDB hack

---

### Phase 2: Test with SD Card Images (2 hours)

Create SD card images and test realistic boot:

```bash
# Create SD images for each platform
./create_qemu_sdcard.sh raspi3b
./create_qemu_sdcard.sh raspi4b

# Test raspi3b with firmware
qemu-system-aarch64 -M raspi3b -sd sdcard_raspi3b.img \
  -serial stdio -nographic

# Test raspi4b with firmware (WILL FAIL - wrong addresses)
qemu-system-aarch64 -M raspi4b -sd sdcard_raspi4b.img \
  -serial stdio -nographic
```

**Expected**: raspi3b may work, raspi4b will fail

---

### Phase 3: Add Hardware Abstraction (4 hours)

1. Add hardware.c and hal.c to Makefile
2. Implement platform detection
3. Update all drivers to use HAL
4. Rebuild and test all platforms

---

### Phase 4: Comprehensive Test Suite (6 hours)

Test all 7 platforms:

```bash
for machine in virt raspi0 raspi1ap raspi2b raspi3ap raspi3b raspi4b; do
    echo "Testing $machine..."
    ./test_qemu.sh $machine
done
```

**Expected**: All pass after hardware abstraction added

---

## VIII. QEMU Limitations per Platform

| Platform | UART | GPIO | Timer | Mailbox | SD Card | USB | Ethernet |
|----------|------|------|-------|---------|---------|-----|----------|
| virt | ✅ Full | ⚠️ Basic | ✅ Full | ❌ No | ⚠️ VirtIO | ⚠️ VirtIO | ⚠️ VirtIO |
| raspi0 | ✅ Full | ⚠️ Reg | ✅ Full | ⚠️ Basic | ⚠️ Limited | ❌ No | ❌ No |
| raspi1ap | ✅ Full | ⚠️ Reg | ✅ Full | ⚠️ Basic | ⚠️ Limited | ❌ No | ❌ No |
| raspi2b | ✅ Full | ⚠️ Reg | ✅ Full | ⚠️ Basic | ⚠️ Limited | ❌ No | ❌ No |
| raspi3ap | ✅ Full | ⚠️ Reg | ✅ Full | ⚠️ Basic | ⚠️ Limited | ❌ No | ❌ No |
| raspi3b | ✅ Full | ⚠️ Reg | ✅ Full | ⚠️ Basic | ⚠️ Limited | ❌ No | ❌ No |
| raspi4b | ✅ Full | ⚠️ Reg | ✅ Full | ⚠️ Basic | ⚠️ Limited | ❌ No | ❌ No |

**Legend**:
- ✅ Full: Complete emulation
- ⚠️ Basic/Reg/Limited: Partial emulation (registers accessible, no real I/O)
- ❌ No: Not emulated

**What can be tested in QEMU**:
- Boot sequence logic ✅
- UART output ✅
- Timer delays ✅
- Memory allocation ✅
- Peripheral register access ✅

**What requires real hardware**:
- GPIO physical I/O ❌
- SD card performance ❌
- USB devices ❌
- Network communication ❌
- Real timing ❌

---

## IX. QEMU Debug Options

### Useful Debug Flags

```bash
-d guest_errors     # Log guest OS errors (invalid accesses)
-d cpu_reset        # Log CPU state on reset
-d int              # Log interrupts
-d unimp            # Log unimplemented features
-d mmu              # Log MMU/page table operations
-D logfile.txt      # Save debug output to file
```

### Example Debug Command

```bash
qemu-system-aarch64 -M raspi3b \
  -sd sdcard.img \
  -serial stdio \
  -nographic \
  -d guest_errors,cpu_reset,int,unimp \
  -D qemu_debug_raspi3b.log
```

**Use for**: Debugging why boot fails on specific platform

---

## X. Next Steps

### Immediate (This Weekend)

1. **Test raspi2b/3b with GDB hack** - Verify current code compatibility
2. **Create SD card images** - For raspi3b and raspi4b
3. **Test with firmware** - See realistic boot behavior

### Short-term (Week 1)

4. **Add hardware.c to build** - Platform detection
5. **Test all 7 platforms** - Comprehensive matrix
6. **Document results** - Update this file with findings

### Medium-term (Week 2)

7. **Fix any platform-specific issues** - Address failures
8. **Optimize for each platform** - Performance tuning
9. **Create automated test suite** - CI/CD for QEMU

---

## XI. Success Criteria

**Goal**: All 7 QEMU platforms boot successfully

| Platform | Target | Current | Status |
|----------|--------|---------|--------|
| virt | Boot + UART | Working | ✅ PASS |
| raspi0 | Boot + UART | Untested | 🔬 TODO |
| raspi1ap | Boot + UART | Untested | 🔬 TODO |
| raspi2b | Boot + UART | Untested | 🔬 TODO |
| raspi3ap | Boot + UART | Untested | 🔬 TODO |
| raspi3b | Boot + UART | Partial | ⚠️ NEED SD |
| raspi4b | Boot + UART | Untested | 🔬 TODO |

**Definition of Success**:
- UART output visible ✅
- Boot sequence completes ✅
- All subsystems initialize ✅
- No guest errors in QEMU log ✅
- Matches expected peripheral behavior ✅

---

**This document will be updated as testing progresses.**
**See N3 ontology: `ontologies/qemu_test_specification.n3` for formal specification.**
