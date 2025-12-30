# Unified BSP Build System
# Build all platform bootloaders from common infrastructure
#
# Usage:
#   make              - Build all platforms (original builds)
#   make unified      - Build all unified builds
#   make virt         - Build QEMU virt only
#   make raspi        - Build Raspberry Pi only
#   make sbsa         - Build SBSA-compatible only
#   make vexpress     - Build ARM Versatile Express only
#   make zynq         - Build Xilinx Zynq only
#   make clean        - Clean all
#   make test         - Run QEMU tests on all platforms
#   make test-unified - Run QEMU tests on unified builds

# Platforms (in order: 64-bit, then 32-bit)
PLATFORMS_64 = virt sbsa raspi zynq
PLATFORMS_32 = vexpress
PLATFORMS = $(PLATFORMS_64) $(PLATFORMS_32)

# Default target
.PHONY: all clean test unified test-unified $(PLATFORMS)

all: $(PLATFORMS)
	@echo ""
	@echo "========================================="
	@echo "  All platforms built successfully"
	@echo "========================================="
	@echo ""
	@for p in $(PLATFORMS); do \
		size=$$(stat -f%z $$p/bootloader-$$p.bin 2>/dev/null || stat -c%s $$p/bootloader-$$p.bin 2>/dev/null || echo "N/A"); \
		printf "  %-12s %s bytes\n" "$$p:" "$$size"; \
	done
	@echo ""

# Individual platform builds
virt:
	@echo "Building QEMU Virt..."
	$(MAKE) -C virt

sbsa:
	@echo "Building ARM SBSA..."
	$(MAKE) -C sbsa

raspi:
	@echo "Building Raspberry Pi..."
	$(MAKE) -C raspi

zynq:
	@echo "Building Xilinx Zynq..."
	$(MAKE) -C zynq

vexpress:
	@echo "Building ARM Versatile Express..."
	$(MAKE) -C vexpress

# Clean all
clean:
	@for p in $(PLATFORMS); do \
		echo "Cleaning $$p..."; \
		$(MAKE) -C $$p clean; \
	done
	@echo "Cleaning common..."
	rm -f common/*.o
	@echo "All cleaned"

# Test all platforms in QEMU
test: all
	@echo ""
	@echo "========================================="
	@echo "  Running QEMU tests"
	@echo "========================================="
	@echo ""
	@echo "Testing virt..."
	@timeout 5 qemu-system-aarch64 -M virt -cpu cortex-a53 -m 256M \
		-kernel virt/bootloader-virt.elf -nographic 2>&1 | head -30 || true
	@echo ""
	@echo "Testing sbsa..."
	@timeout 5 qemu-system-aarch64 -M virt -cpu cortex-a57 -m 4G \
		-kernel sbsa/bootloader-sbsa.elf -nographic 2>&1 | head -30 || true
	@echo ""
	@echo "Testing vexpress..."
	@timeout 5 qemu-system-arm -M vexpress-a15 -cpu cortex-a15 -m 1024M \
		-kernel vexpress/bootloader-vexpress.elf -nographic 2>&1 | head -30 || true
	@echo ""
	@echo "Testing zynq..."
	@timeout 5 qemu-system-aarch64 -M xlnx-zcu102 \
		-kernel zynq/bootloader-zynq.elf -nographic 2>&1 | head -30 || true
	@echo ""
	@echo "Testing raspi..."
	@timeout 5 qemu-system-aarch64 -M raspi3b \
		-kernel raspi/bootloader-raspi.elf -nographic 2>&1 | head -30 || true
	@echo ""
	@echo "========================================="
	@echo "  All QEMU tests complete"
	@echo "========================================="

# Unified builds (using Makefile.unified in each platform)
unified:
	@echo ""
	@echo "========================================="
	@echo "  Building Unified BSPs"
	@echo "========================================="
	@echo ""
	@for p in $(PLATFORMS); do \
		echo "Building $$p (unified)..."; \
		$(MAKE) -C $$p -f Makefile.unified; \
	done
	@echo ""
	@echo "========================================="
	@echo "  Unified builds complete"
	@echo "========================================="
	@echo ""
	@for p in $(PLATFORMS); do \
		size=$$(stat -f%z $$p/bootloader-$$p-unified.bin 2>/dev/null || stat -c%s $$p/bootloader-$$p-unified.bin 2>/dev/null || echo "N/A"); \
		printf "  %-12s %s bytes\n" "$$p:" "$$size"; \
	done
	@echo ""

# Test unified builds
test-unified: unified
	@echo ""
	@echo "========================================="
	@echo "  Testing Unified Builds"
	@echo "========================================="
	@echo ""
	@echo "Testing virt (unified)..."
	@timeout 5 qemu-system-aarch64 -M virt -cpu cortex-a53 -m 256M \
		-kernel virt/bootloader-virt-unified.elf -nographic 2>&1 | head -30 || true
	@echo ""
	@echo "Testing sbsa (unified)..."
	@timeout 5 qemu-system-aarch64 -M virt -cpu cortex-a57 -m 4G \
		-kernel sbsa/bootloader-sbsa-unified.elf -nographic 2>&1 | head -30 || true
	@echo ""
	@echo "Testing vexpress (unified)..."
	@timeout 5 qemu-system-arm -M vexpress-a15 -cpu cortex-a15 -m 1024M \
		-kernel vexpress/bootloader-vexpress-unified.elf -nographic 2>&1 | head -30 || true
	@echo ""
	@echo "Testing zynq (unified)..."
	@timeout 5 qemu-system-aarch64 -M xlnx-zcu102 \
		-kernel zynq/bootloader-zynq-unified.elf -nographic 2>&1 | head -30 || true
	@echo ""
	@echo "Testing raspi (unified)..."
	@timeout 5 qemu-system-aarch64 -M raspi3b \
		-kernel raspi/bootloader-raspi-unified.elf -nographic 2>&1 | head -30 || true
	@echo ""
	@echo "========================================="
	@echo "  All unified tests complete"
	@echo "========================================="

# Summary
info:
	@echo "ARM Bootloader - Unified Build System"
	@echo ""
	@echo "Platforms:"
	@echo "  64-bit: $(PLATFORMS_64)"
	@echo "  32-bit: $(PLATFORMS_32)"
	@echo ""
	@echo "Common files: common/"
	@echo "  - bsp.h           : BSP interface"
	@echo "  - kernel_boot.h   : Kernel boot interface"
	@echo "  - boot_common.h/c : Shared boot logic"
	@echo "  - kernel_boot_arm64.S : ARM64 boot assembly"
	@echo "  - kernel_boot_arm32.S : ARM32 boot assembly"
