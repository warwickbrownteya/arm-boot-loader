# Makefile for Xilinx Zynq UltraScale+ Bootloader

CROSS_COMPILE ?= aarch64-elf-
CC = $(CROSS_COMPILE)gcc
AS = $(CROSS_COMPILE)as
LD = $(CROSS_COMPILE)ld
OBJCOPY = $(CROSS_COMPILE)objcopy

CFLAGS = -Wall -Wextra -Os -ffreestanding -nostdlib -nostartfiles
CFLAGS += -I../common -I.
ASFLAGS = -march=armv8-a
LDFLAGS = -T linker.ld

TARGET = bootloader-zynq.bin
ELF = bootloader-zynq.elf

SRC_C = main_zynq.c bsp_zynq.c
SRC_S = start.S kernel_boot.S
OBJ = $(SRC_C:.c=.o) $(SRC_S:.S=.o)

.PHONY: all clean qemu

all: $(TARGET)

$(TARGET): $(ELF)
	$(OBJCOPY) -O binary $< $@
	@echo "Built: $(TARGET) ($$(stat -f%z $(TARGET) 2>/dev/null || stat -c%s $(TARGET)) bytes)"

$(ELF): $(OBJ) linker.ld
	$(LD) $(LDFLAGS) -o $@ $(OBJ)

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

%.o: %.S
	$(AS) $(ASFLAGS) $< -o $@

clean:
	rm -f $(OBJ) $(ELF) $(TARGET)
	@echo "Cleaned build artifacts"

qemu: $(ELF)
	@echo "Running bootloader on QEMU Zynq ZCU102..."
	qemu-system-aarch64 -M xlnx-zcu102 \
		-kernel $(ELF) -nographic -serial mon:stdio

qemu-debug: $(ELF)
	@echo "Running bootloader on QEMU Zynq ZCU102 (debug mode)..."
	qemu-system-aarch64 -M xlnx-zcu102 \
		-kernel $(ELF) -nographic -serial mon:stdio -S -s
