# Makefile for ARM Versatile Express A15 Bootloader (32-bit ARMv7-A)

CROSS_COMPILE ?= arm-none-eabi-
CC = $(CROSS_COMPILE)gcc
AS = $(CROSS_COMPILE)as
LD = $(CROSS_COMPILE)ld
OBJCOPY = $(CROSS_COMPILE)objcopy

# ARMv7-A flags for Cortex-A15
CFLAGS = -Wall -Wextra -Os -ffreestanding -nostdlib -nostartfiles
CFLAGS += -mcpu=cortex-a15 -marm
CFLAGS += -I../common -I.
ASFLAGS = -mcpu=cortex-a15
LDFLAGS = -T linker.ld

TARGET = bootloader-vexpress.bin
ELF = bootloader-vexpress.elf

SRC_C = main_vexpress.c bsp_vexpress.c
SRC_S = start.S kernel_boot.S
OBJ = $(SRC_C:.c=.o) $(SRC_S:.S=.o)

.PHONY: all clean qemu

all: $(TARGET)

$(TARGET): $(ELF)
	$(OBJCOPY) -O binary $< $@
	@echo "Built: $(TARGET) ($$(stat -f%z $(TARGET) 2>/dev/null || stat -c%s $(TARGET)) bytes)"
	@echo "Architecture: ARMv7-A (32-bit) for Cortex-A15"

$(ELF): $(OBJ) linker.ld
	$(LD) $(LDFLAGS) -o $@ $(OBJ)

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

%.o: %.S
	$(AS) $(ASFLAGS) $< -o $@

clean:
	rm -f $(OBJ) $(ELF) $(TARGET)
	@echo "Cleaned build artifacts"

# QEMU with 32-bit ARM vexpress-a15
qemu: $(ELF)
	@echo "Running bootloader on QEMU Versatile Express A15 (32-bit)..."
	qemu-system-arm -M vexpress-a15 -cpu cortex-a15 -m 1024M \
		-kernel $(ELF) -nographic -serial mon:stdio

qemu-debug: $(ELF)
	@echo "Running bootloader on QEMU Versatile Express A15 (debug mode)..."
	qemu-system-arm -M vexpress-a15 -cpu cortex-a15 -m 1024M \
		-kernel $(ELF) -nographic -serial mon:stdio -S -s
