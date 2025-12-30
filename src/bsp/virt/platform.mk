# Platform configuration for QEMU Virt Machine

PLATFORM_NAME = virt
PLATFORM_DESC = QEMU ARM Virtual Machine

# Load address
LOAD_ADDR = 0x40000000

# Platform-specific source files
BSP_SRC = bsp/virt/bsp_virt.c
BSP_ASM = bsp/virt/start.S

# Linker script
LINKER_SCRIPT = bsp/virt/linker.ld

# Output binary name
TARGET = bootloader-virt.bin
ELF = bootloader-virt.elf

# QEMU configuration
QEMU_MACHINE = virt
QEMU_CPU = cortex-a53
QEMU_MEMORY = 128M
QEMU_OPTS = -M $(QEMU_MACHINE) -cpu $(QEMU_CPU) -m $(QEMU_MEMORY) -nographic

# Test command
qemu-virt:
	@echo "Running bootloader on QEMU Virt..."
	qemu-system-aarch64 $(QEMU_OPTS) -kernel $(ELF) -serial mon:stdio
