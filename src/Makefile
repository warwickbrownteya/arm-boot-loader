# Raspberry Pi Bootloader Makefile
# Supports: Pi 3 (raspi3b, raspi3ap) and Pi 4 (raspi4b)

CROSS_COMPILE ?= aarch64-elf-
CC = $(CROSS_COMPILE)gcc
AS = $(CROSS_COMPILE)as
LD = $(CROSS_COMPILE)ld
OBJCOPY = $(CROSS_COMPILE)objcopy

# Target Pi model: pi3 (default) or pi4
PI_MODEL ?= pi3

# Peripheral base addresses
ifeq ($(PI_MODEL),pi4)
    PERIPHERAL_BASE = 0xFE000000
    TARGET = bootloader-pi4.bin
else
    PERIPHERAL_BASE = 0x3F000000
    TARGET = bootloader.bin
endif

CFLAGS = -Wall -Wextra -Os -ffreestanding -nostdlib -nostartfiles -DPERIPHERAL_BASE=$(PERIPHERAL_BASE)
ASFLAGS = -march=armv8-a
LDFLAGS = -T linker.ld

# Minimal source files
SRC_C = main.c uart.c timer.c gpio.c memory.c mailbox.c sd.c hardware.c fsa_monitor.c verification.c
SRC_S = start.S
OBJ = $(SRC_C:.c=.o) $(SRC_S:.S=.o)

ELF = bootloader.elf

.PHONY: all clean qemu-test qemu-pi3 qemu-pi4 pi3 pi4

all: $(TARGET)

# Build for Pi 3 (default)
pi3:
	$(MAKE) PI_MODEL=pi3

# Build for Pi 4
pi4:
	$(MAKE) PI_MODEL=pi4

$(TARGET): $(ELF)
	$(OBJCOPY) -O binary $< $@
	@echo "Built: $(TARGET) for $(PI_MODEL) ($$(stat -f%z $(TARGET) 2>/dev/null || stat -c%s $(TARGET)) bytes)"

$(ELF): $(OBJ) linker.ld
	$(LD) $(LDFLAGS) -o $@ $(OBJ)

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

%.o: %.S
	$(AS) $(ASFLAGS) $< -o $@

clean:
	rm -f $(OBJ) bootloader.elf bootloader.bin bootloader-pi4.bin
	@echo "Cleaned build artifacts"

# QEMU tests
qemu-test: qemu-pi3

qemu-pi3: pi3
	@echo "Running bootloader in QEMU (raspi3b)..."
	qemu-system-aarch64 -M raspi3b -kernel bootloader.bin -serial stdio -nographic

qemu-pi4: pi4
	@echo "Running bootloader in QEMU (raspi4b)..."
	qemu-system-aarch64 -M raspi4b -kernel bootloader-pi4.bin -serial stdio -nographic
