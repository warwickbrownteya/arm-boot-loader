# Makefile for ARM SBSA-Compatible Platform Bootloader
#
# Uses QEMU 'virt' machine for testing (RAM at 0x40000000)
# Supports up to 8GB RAM within reliable GOT addressing range

CROSS_COMPILE ?= aarch64-elf-
CC = $(CROSS_COMPILE)gcc
AS = $(CROSS_COMPILE)as
LD = $(CROSS_COMPILE)ld
OBJCOPY = $(CROSS_COMPILE)objcopy

# AArch64 flags for server-class Cortex-A
# Note: -mcmodel=small (default) is sufficient for addresses < 4GB
CFLAGS = -Wall -Wextra -Os -ffreestanding -nostdlib -nostartfiles
CFLAGS += -mcpu=cortex-a57 -mabi=lp64
CFLAGS += -I../common -I.
ASFLAGS = -mcpu=cortex-a57
LDFLAGS = -T linker.ld

TARGET = bootloader-sbsa.bin
ELF = bootloader-sbsa.elf

SRC_C = main_sbsa.c bsp_sbsa.c
SRC_S = start.S kernel_boot.S
OBJ = $(SRC_C:.c=.o) $(SRC_S:.S=.o)

.PHONY: all clean qemu

all: $(TARGET)

$(TARGET): $(ELF)
	$(OBJCOPY) -O binary $< $@
	@echo "Built: $(TARGET) ($$(stat -f%z $(TARGET) 2>/dev/null || stat -c%s $(TARGET)) bytes)"
	@echo "Architecture: AArch64 (64-bit) SBSA-compatible (8GB max)"

$(ELF): $(OBJ) linker.ld
	$(LD) $(LDFLAGS) -o $@ $(OBJ)

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

%.o: %.S
	$(AS) $(ASFLAGS) $< -o $@

clean:
	rm -f $(OBJ) $(ELF) $(TARGET)
	@echo "Cleaned build artifacts"

# QEMU with virt machine (SBSA-compatible peripherals)
qemu: $(ELF)
	@echo "Running SBSA-compatible bootloader on QEMU virt machine..."
	qemu-system-aarch64 -M virt -cpu cortex-a57 -m 4G \
		-kernel $(ELF) -nographic

qemu-debug: $(ELF)
	@echo "Running bootloader in debug mode..."
	qemu-system-aarch64 -M virt -cpu cortex-a57 -m 4G \
		-kernel $(ELF) -nographic -S -s
