# Makefile for ARM Raspberry Pi 3 Bootloader
#
# Uses QEMU raspi3b machine for testing
# Entry point at 0x80000 (set by GPU firmware)

CROSS_COMPILE ?= aarch64-elf-
CC = $(CROSS_COMPILE)gcc
AS = $(CROSS_COMPILE)as
LD = $(CROSS_COMPILE)ld
OBJCOPY = $(CROSS_COMPILE)objcopy

# AArch64 flags for Cortex-A53
CFLAGS = -Wall -Wextra -Os -ffreestanding -nostdlib -nostartfiles
CFLAGS += -mcpu=cortex-a53 -mabi=lp64
CFLAGS += -I../common -I.
ASFLAGS = -mcpu=cortex-a53
LDFLAGS = -T linker.ld

# Output files
# Note: Real Pi boots kernel8.img, but we use .bin for consistency
TARGET = bootloader-raspi.bin
ELF = bootloader-raspi.elf

SRC_C = main_raspi.c bsp_raspi.c sd.c
SRC_S = start.S kernel_boot.S
OBJ = $(SRC_C:.c=.o) $(SRC_S:.S=.o)

.PHONY: all clean qemu kernel8

all: $(TARGET)

$(TARGET): $(ELF)
	$(OBJCOPY) -O binary $< $@
	@echo "Built: $(TARGET) ($$(stat -f%z $(TARGET) 2>/dev/null || stat -c%s $(TARGET)) bytes)"
	@echo "Architecture: AArch64 (64-bit) Raspberry Pi 3"

# Also create kernel8.img for real hardware
kernel8: $(TARGET)
	cp $(TARGET) kernel8.img
	@echo "Created kernel8.img for Raspberry Pi 3"

$(ELF): $(OBJ) linker.ld
	$(LD) $(LDFLAGS) -o $@ $(OBJ)

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

%.o: %.S
	$(AS) $(ASFLAGS) $< -o $@

clean:
	rm -f $(OBJ) $(ELF) $(TARGET) kernel8.img
	@echo "Cleaned build artifacts"

# QEMU test with raspi3b machine
qemu: $(ELF)
	@echo "Running bootloader on QEMU Raspberry Pi 3B..."
	qemu-system-aarch64 -M raspi3b -cpu cortex-a53 \
		-kernel $(ELF) -nographic -serial mon:stdio

qemu-debug: $(ELF)
	@echo "Running bootloader in debug mode..."
	qemu-system-aarch64 -M raspi3b -cpu cortex-a53 \
		-kernel $(ELF) -nographic -S -s
