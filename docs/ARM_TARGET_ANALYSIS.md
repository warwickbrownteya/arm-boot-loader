# ARM Target Analysis for Bootloader Porting

## Executive Summary

This document analyzes QEMU-supported ARM targets for potential bootloader porting,
defining Board Support Packages (BSPs) for each viable platform.

## Current Support

| Platform | Machine | Status | Peripheral Base |
|----------|---------|--------|-----------------|
| Raspberry Pi 3B | raspi3b | Supported | 0x3F000000 |
| Raspberry Pi 3A+ | raspi3ap | Supported | 0x3F000000 |
| Raspberry Pi 4B | raspi4b | Supported | 0xFE000000 |

## Candidate Platforms for Porting

### Tier 1: High Priority (Well-Supported, Good QEMU Emulation)

#### 1. QEMU Virt Machine (`virt`)
- **CPU**: Configurable (Cortex-A53, A72, etc.)
- **Architecture**: AArch64
- **Load Address**: 0x40000000
- **UART**: PL011 at 0x09000000
- **Timer**: ARM Generic Timer
- **Interrupt Controller**: GICv2/v3 at 0x08000000
- **Storage**: VirtIO block devices at 0x0A000000+
- **Difficulty**: Medium
- **Notes**: Standard ARM virtual machine, excellent for testing

#### 2. Xilinx Zynq UltraScale+ ZCU102 (`xlnx-zcu102`)
- **CPU**: Quad Cortex-A53 + Dual Cortex-R5F
- **Architecture**: AArch64
- **Load Address**: 0x00000000 (OCM) or 0x00100000 (DDR)
- **UART**: Cadence UART at 0xFF000000 (UART0), 0xFF010000 (UART1)
- **Timer**: TTC at 0xFF110000
- **Interrupt Controller**: GICv2
- **Storage**: SD/eMMC via SDHCI
- **Difficulty**: Medium-High
- **Notes**: Popular FPGA SoC platform

#### 3. ARM Versatile Express A15 (`vexpress-a15`)
- **CPU**: Cortex-A15
- **Architecture**: AArch32 (ARMv7-A)
- **Load Address**: 0x80000000
- **UART**: PL011 at 0x1C090000
- **Timer**: SP804 at 0x1C110000
- **Interrupt Controller**: GIC at 0x2C000000
- **Storage**: PL180 MMC
- **Difficulty**: Medium
- **Notes**: ARM reference platform

#### 4. NXP i.MX 8M Plus (`imx8mp-evk`)
- **CPU**: Quad Cortex-A53
- **Architecture**: AArch64
- **Load Address**: 0x40200000
- **UART**: NXP LPUART at 0x30860000
- **Timer**: ARM Generic Timer
- **Interrupt Controller**: GICv3
- **Storage**: uSDHC
- **Difficulty**: High
- **Notes**: Modern NXP application processor

### Tier 2: Medium Priority (Specialized Platforms)

#### 5. SBSA Reference Platform (`sbsa-ref`)
- **CPU**: Configurable Cortex-A series
- **Architecture**: AArch64
- **Load Address**: 0x10000000000 (high memory)
- **UART**: PL011
- **Notes**: ARM Server Base System Architecture reference

#### 6. Xilinx Versal (`xlnx-versal-virt`)
- **CPU**: Dual Cortex-A72 + Dual Cortex-R5
- **Architecture**: AArch64
- **UART**: Cadence UART
- **Notes**: Latest Xilinx architecture with AI engines

#### 7. Orange Pi PC (`orangepi-pc`)
- **CPU**: Allwinner H3 (Quad Cortex-A7)
- **Architecture**: AArch32
- **UART**: Allwinner UART at 0x01C28000
- **Notes**: Popular SBC platform

#### 8. Cubieboard (`cubieboard`)
- **CPU**: Allwinner A10 (Cortex-A8)
- **Architecture**: AArch32
- **UART**: Allwinner UART
- **Notes**: Early ARM SBC

### Tier 3: Lower Priority (BMC/Specialized)

- Aspeed AST2600 EVB (BMC platform)
- Various Facebook/Meta BMC boards
- Samsung Exynos boards (NURI, SMDKC210)

---

## BSP Definitions

### BSP Structure

```
bsp/
├── common/
│   ├── bsp.h           # Common BSP interface
│   ├── uart_common.h   # UART abstraction
│   └── timer_common.h  # Timer abstraction
├── raspi/
│   ├── bsp_raspi.c     # Raspberry Pi BSP
│   ├── uart_bcm.c      # BCM283x/BCM2711 UART
│   ├── timer_bcm.c     # BCM system timer
│   ├── gpio_bcm.c      # BCM GPIO
│   ├── mailbox_bcm.c   # VideoCore mailbox
│   └── emmc_bcm.c      # BCM EMMC
├── virt/
│   ├── bsp_virt.c      # QEMU Virt BSP
│   ├── uart_pl011.c    # ARM PL011 UART
│   ├── timer_generic.c # ARM Generic Timer
│   ├── gic.c           # GIC driver
│   └── virtio_blk.c    # VirtIO block
├── zynq/
│   ├── bsp_zynq.c      # Zynq UltraScale+ BSP
│   ├── uart_cadence.c  # Cadence UART
│   ├── timer_ttc.c     # Triple Timer Counter
│   └── sdhci.c         # SDHCI driver
└── vexpress/
    ├── bsp_vexpress.c  # Versatile Express BSP
    ├── uart_pl011.c    # Shared with virt
    └── timer_sp804.c   # SP804 timer
```

---

## BSP 1: QEMU Virt Machine

### Memory Map
```
0x00000000 - 0x03FFFFFF : Flash 0 (64MB)
0x04000000 - 0x07FFFFFF : Flash 1 (64MB)
0x08000000 - 0x08000FFF : GIC Distributor
0x08010000 - 0x08011FFF : GIC CPU Interface
0x09000000 - 0x09000FFF : PL011 UART
0x09010000 - 0x09010FFF : PL031 RTC
0x09030000 - 0x09030FFF : PL061 GPIO
0x0A000000 - 0x0A003FFF : VirtIO MMIO (32 slots)
0x40000000 - 0x47FFFFFF : RAM (128MB default)
```

### PL011 UART Registers
```c
#define UART_BASE       0x09000000
#define UART_DR         (UART_BASE + 0x00)  // Data Register
#define UART_FR         (UART_BASE + 0x18)  // Flag Register
#define UART_IBRD       (UART_BASE + 0x24)  // Integer Baud Rate
#define UART_FBRD       (UART_BASE + 0x28)  // Fractional Baud Rate
#define UART_LCR_H      (UART_BASE + 0x2C)  // Line Control
#define UART_CR         (UART_BASE + 0x30)  // Control Register
#define UART_IMSC       (UART_BASE + 0x38)  // Interrupt Mask

// Flag Register bits
#define UART_FR_TXFF    (1 << 5)  // TX FIFO Full
#define UART_FR_RXFE    (1 << 4)  // RX FIFO Empty
```

### Linker Script Changes
```ld
. = 0x40000000; /* Virt machine RAM start */
```

### Required BSP Files

**bsp/virt/uart_pl011.c:**
```c
#define PL011_BASE 0x09000000

void uart_init(void) {
    // PL011 UART initialization
    mmio_write(PL011_BASE + 0x30, 0x0);     // Disable UART
    mmio_write(PL011_BASE + 0x24, 1);       // IBRD = 1 (115200 @ 24MHz)
    mmio_write(PL011_BASE + 0x28, 40);      // FBRD
    mmio_write(PL011_BASE + 0x2C, 0x70);    // 8N1, FIFO enable
    mmio_write(PL011_BASE + 0x30, 0x301);   // Enable UART, TX, RX
}

void uart_putc(char c) {
    while (mmio_read(PL011_BASE + 0x18) & (1 << 5)); // Wait TX ready
    mmio_write(PL011_BASE + 0x00, c);
}
```

---

## BSP 2: Xilinx Zynq UltraScale+ (ZCU102)

### Memory Map
```
0x00000000 - 0x0003FFFF : OCM (256KB)
0x00100000 - 0x7FFFFFFF : DDR Low (2GB)
0x800000000 - ...       : DDR High
0xFD000000 - 0xFDFFFFFF : Full Power Domain peripherals
0xFE000000 - 0xFEFFFFFF : Low Power Domain peripherals
0xFF000000 - 0xFF00FFFF : UART0
0xFF010000 - 0xFF01FFFF : UART1
0xFF110000 - 0xFF11FFFF : TTC0
0xFF0A0000 - 0xFF0AFFFF : GPIO
0xFF160000 - 0xFF16FFFF : SD0 (SDHCI)
0xFF170000 - 0xFF17FFFF : SD1 (SDHCI)
```

### Cadence UART Registers
```c
#define UART0_BASE      0xFF000000
#define UART_CR         (UART0_BASE + 0x00)  // Control
#define UART_MR         (UART0_BASE + 0x04)  // Mode
#define UART_IER        (UART0_BASE + 0x08)  // Interrupt Enable
#define UART_IDR        (UART0_BASE + 0x0C)  // Interrupt Disable
#define UART_SR         (UART0_BASE + 0x2C)  // Status
#define UART_FIFO       (UART0_BASE + 0x30)  // TX/RX FIFO
#define UART_BRGR       (UART0_BASE + 0x18)  // Baud Rate Generator
#define UART_BDIV       (UART0_BASE + 0x34)  // Baud Rate Divider

// Status Register bits
#define UART_SR_TXFULL  (1 << 4)
#define UART_SR_RXEMPTY (1 << 1)
```

### Required BSP Files

**bsp/zynq/uart_cadence.c:**
```c
#define CADENCE_UART_BASE 0xFF000000

void uart_init(void) {
    // Reset and configure Cadence UART
    mmio_write(CADENCE_UART_BASE + 0x00, 0x28);  // Reset TX/RX
    mmio_write(CADENCE_UART_BASE + 0x04, 0x20);  // 8N1, normal mode
    mmio_write(CADENCE_UART_BASE + 0x18, 62);    // Baud rate divisor
    mmio_write(CADENCE_UART_BASE + 0x34, 6);     // Clock divisor
    mmio_write(CADENCE_UART_BASE + 0x00, 0x14);  // Enable TX/RX
}

void uart_putc(char c) {
    while (mmio_read(CADENCE_UART_BASE + 0x2C) & (1 << 4)); // TX full
    mmio_write(CADENCE_UART_BASE + 0x30, c);
}
```

---

## BSP 3: ARM Versatile Express A15

### Memory Map
```
0x00000000 - 0x03FFFFFF : NOR Flash
0x08000000 - 0x0BFFFFFF : PSRAM
0x1C010000 - 0x1C01FFFF : System Controller
0x1C090000 - 0x1C09FFFF : UART0 (PL011)
0x1C0A0000 - 0x1C0AFFFF : UART1 (PL011)
0x1C110000 - 0x1C11FFFF : Timer (SP804)
0x1C050000 - 0x1C05FFFF : MMC (PL180)
0x2C000000 - 0x2C00FFFF : GIC Distributor
0x2C010000 - 0x2C01FFFF : GIC CPU Interface
0x80000000 - 0xFFFFFFFF : DDR RAM
```

### SP804 Timer Registers
```c
#define SP804_BASE      0x1C110000
#define TIMER1_LOAD     (SP804_BASE + 0x00)
#define TIMER1_VALUE    (SP804_BASE + 0x04)
#define TIMER1_CONTROL  (SP804_BASE + 0x08)
#define TIMER1_INTCLR   (SP804_BASE + 0x0C)

// Control bits
#define TIMER_EN        (1 << 7)
#define TIMER_PERIODIC  (1 << 6)
#define TIMER_32BIT     (1 << 1)
```

---

## BSP 4: NXP i.MX 8M Plus

### Memory Map
```
0x30000000 - 0x30FFFFFF : AIPS1 Peripherals
0x30200000 - 0x302FFFFF : AIPS2 Peripherals
0x30400000 - 0x304FFFFF : AIPS3 Peripherals
0x30800000 - 0x308FFFFF : AIPS4 Peripherals
0x30860000 - 0x30863FFF : UART1
0x30890000 - 0x30893FFF : UART2
0x30A20000 - 0x30A2FFFF : uSDHC1
0x30A30000 - 0x30A3FFFF : uSDHC2
0x38800000 - 0x38FFFFFF : GIC
0x40000000 - 0xBFFFFFFF : DDR (2GB)
```

### NXP LPUART Registers
```c
#define LPUART1_BASE    0x30860000
#define LPUART_GLOBAL   (LPUART1_BASE + 0x08)
#define LPUART_CTRL     (LPUART1_BASE + 0x18)
#define LPUART_STAT     (LPUART1_BASE + 0x14)
#define LPUART_DATA     (LPUART1_BASE + 0x1C)
#define LPUART_BAUD     (LPUART1_BASE + 0x10)
```

---

## Implementation Priority

### Phase 1: QEMU Virt Machine
1. Create `bsp/virt/` directory structure
2. Implement PL011 UART driver
3. Implement ARM Generic Timer driver
4. Create virt-specific linker script
5. Test in QEMU

### Phase 2: Xilinx Zynq
1. Create `bsp/zynq/` directory structure
2. Implement Cadence UART driver
3. Implement TTC timer driver
4. Port to xlnx-zcu102

### Phase 3: Versatile Express
1. Reuse PL011 driver from virt
2. Implement SP804 timer
3. Implement PL180 MMC driver

### Phase 4: i.MX 8M Plus
1. Implement LPUART driver
2. Implement uSDHC driver
3. Port to imx8mp-evk

---

## Build System Changes

### Makefile Updates
```makefile
# Target platform selection
PLATFORM ?= raspi

ifeq ($(PLATFORM),raspi)
    include bsp/raspi/platform.mk
else ifeq ($(PLATFORM),virt)
    include bsp/virt/platform.mk
else ifeq ($(PLATFORM),zynq)
    include bsp/zynq/platform.mk
else ifeq ($(PLATFORM),vexpress)
    include bsp/vexpress/platform.mk
endif

# Platform-specific includes
CFLAGS += -I bsp/$(PLATFORM) -I bsp/common
```

### Platform Config Files
**bsp/virt/platform.mk:**
```makefile
LOAD_ADDR = 0x40000000
UART_DRIVER = uart_pl011.c
TIMER_DRIVER = timer_generic.c
LINKER_SCRIPT = bsp/virt/linker.ld
QEMU_MACHINE = virt
QEMU_CPU = cortex-a53
```

---

## Testing Matrix

| Platform | QEMU Machine | CPU | Test Status |
|----------|--------------|-----|-------------|
| Raspberry Pi 3B | raspi3b | Cortex-A53 | PASS |
| Raspberry Pi 3A+ | raspi3ap | Cortex-A53 | PASS |
| Raspberry Pi 4B | raspi4b | Cortex-A72 | PASS |
| QEMU Virt | virt | Cortex-A53 | Pending |
| Zynq ZCU102 | xlnx-zcu102 | Cortex-A53 | Pending |
| Versatile Express | vexpress-a15 | Cortex-A15 | Pending |
| i.MX 8M Plus | imx8mp-evk | Cortex-A53 | Pending |

---

## Appendix: QEMU Test Commands

```bash
# QEMU Virt
qemu-system-aarch64 -M virt -cpu cortex-a53 -m 128M \
    -kernel bootloader-virt.elf -nographic

# Xilinx Zynq
qemu-system-aarch64 -M xlnx-zcu102 \
    -kernel bootloader-zynq.elf -nographic

# Versatile Express (32-bit)
qemu-system-arm -M vexpress-a15 \
    -kernel bootloader-vexpress.elf -nographic

# i.MX 8M Plus
qemu-system-aarch64 -M imx8mp-evk \
    -kernel bootloader-imx8.elf -nographic
```
