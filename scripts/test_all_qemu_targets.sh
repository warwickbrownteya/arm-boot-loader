#!/bin/bash
# Comprehensive QEMU Target Testing Script
# Tests bootloader on all 7 QEMU ARM platforms

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Test duration (seconds)
TEST_DURATION=5

# Results directory
RESULTS_DIR="qemu_test_results"
mkdir -p "$RESULTS_DIR"

echo -e "${BLUE}========================================${NC}"
echo -e "${BLUE}  QEMU ARM Platform Test Suite${NC}"
echo -e "${BLUE}  Testing bootloader on 7 targets${NC}"
echo -e "${BLUE}========================================${NC}"
echo ""

# Check bootloader exists
if [ ! -f "bootloader.bin" ]; then
    echo -e "${RED}Error: bootloader.bin not found${NC}"
    echo "Run 'make' first"
    exit 1
fi

BOOTLOADER_SIZE=$(stat -f%z bootloader.bin 2>/dev/null || stat -c%s bootloader.bin)
echo -e "Bootloader: bootloader.bin (${BOOTLOADER_SIZE} bytes)"
echo ""

# Array to store results
declare -A TEST_RESULTS
declare -A TEST_OUTPUTS

# Test function
test_qemu_target() {
    local MACHINE=$1
    local CPU=$2
    local MEMORY=$3
    local EXTRA_ARGS=$4

    echo -e "${YELLOW}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo -e "${YELLOW}Testing: $MACHINE${NC}"
    echo -e "${YELLOW}CPU: $CPU, Memory: $MEMORY${NC}"
    echo -e "${YELLOW}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"

    local OUTPUT_FILE="$RESULTS_DIR/${MACHINE}_output.log"
    local DEBUG_FILE="$RESULTS_DIR/${MACHINE}_debug.log"

    # Run QEMU in background
    qemu-system-aarch64 \
        -M "$MACHINE" \
        -cpu "$CPU" \
        -m "$MEMORY" \
        -kernel bootloader.bin \
        -nographic \
        -d guest_errors,cpu_reset \
        -D "$DEBUG_FILE" \
        $EXTRA_ARGS \
        > "$OUTPUT_FILE" 2>&1 &

    local QEMU_PID=$!

    # Wait for test duration
    sleep $TEST_DURATION

    # Kill QEMU
    kill $QEMU_PID 2>/dev/null || true
    wait $QEMU_PID 2>/dev/null || true

    # Analyze results
    local OUTPUT=$(cat "$OUTPUT_FILE")
    local DEBUG=$(cat "$DEBUG_FILE")

    # Check for UART output
    if echo "$OUTPUT" | grep -q "Minimal ARM Bootloader"; then
        TEST_RESULTS[$MACHINE]="PASS"
        echo -e "${GREEN}✓ PASS${NC} - UART output detected"
        TEST_OUTPUTS[$MACHINE]=$(echo "$OUTPUT" | head -10)
    elif echo "$OUTPUT" | grep -q "========"; then
        TEST_RESULTS[$MACHINE]="PARTIAL"
        echo -e "${YELLOW}⚠ PARTIAL${NC} - Some output detected"
        TEST_OUTPUTS[$MACHINE]=$(echo "$OUTPUT" | head -10)
    elif echo "$DEBUG" | grep -q "PC=0000000000080000"; then
        TEST_RESULTS[$MACHINE]="CPU_START"
        echo -e "${YELLOW}⚠ CPU_START${NC} - CPU started but no UART output"
        TEST_OUTPUTS[$MACHINE]="CPU reached entry point (PC=0x80000) but no UART"
    elif echo "$DEBUG" | grep -q "CPU Reset"; then
        TEST_RESULTS[$MACHINE]="CPU_RESET"
        echo -e "${RED}✗ CPU_RESET${NC} - CPU reset but didn't start execution"
        TEST_OUTPUTS[$MACHINE]="CPU reset detected, but execution didn't begin"
    else
        TEST_RESULTS[$MACHINE]="FAIL"
        echo -e "${RED}✗ FAIL${NC} - No activity detected"
        TEST_OUTPUTS[$MACHINE]="No output or CPU activity"
    fi

    echo ""
    echo "Output preview:"
    head -5 "$OUTPUT_FILE" || echo "(no output)"
    echo ""
    echo "Debug info:"
    head -3 "$DEBUG_FILE" | grep "PC=" || echo "(no PC info)"
    echo ""
}

# =============================================================================
# Test 1: virt - QEMU ARM Virtual Machine
# =============================================================================

test_qemu_target "virt" "cortex-a72" "1G" ""

# =============================================================================
# Test 2: raspi0 - Raspberry Pi Zero
# =============================================================================

test_qemu_target "raspi0" "arm1176" "512M" ""

# =============================================================================
# Test 3: raspi1ap - Raspberry Pi A+
# =============================================================================

test_qemu_target "raspi1ap" "arm1176" "512M" ""

# =============================================================================
# Test 4: raspi2b - Raspberry Pi 2B
# =============================================================================

test_qemu_target "raspi2b" "cortex-a7" "1G" ""

# =============================================================================
# Test 5: raspi3ap - Raspberry Pi 3A+
# =============================================================================

test_qemu_target "raspi3ap" "cortex-a53" "512M" ""

# =============================================================================
# Test 6: raspi3b - Raspberry Pi 3B
# =============================================================================

test_qemu_target "raspi3b" "cortex-a53" "1G" ""

# =============================================================================
# Test 7: raspi4b - Raspberry Pi 4B
# =============================================================================

test_qemu_target "raspi4b" "cortex-a72" "4G" ""

# =============================================================================
# Summary Report
# =============================================================================

echo ""
echo -e "${BLUE}========================================${NC}"
echo -e "${BLUE}  TEST SUMMARY${NC}"
echo -e "${BLUE}========================================${NC}"
echo ""

PASS_COUNT=0
FAIL_COUNT=0
PARTIAL_COUNT=0
CPU_START_COUNT=0
CPU_RESET_COUNT=0

for machine in virt raspi0 raspi1ap raspi2b raspi3ap raspi3b raspi4b; do
    result="${TEST_RESULTS[$machine]}"

    printf "%-12s " "$machine"

    case "$result" in
        PASS)
            echo -e "${GREEN}✓ PASS${NC}"
            ((PASS_COUNT++))
            ;;
        PARTIAL)
            echo -e "${YELLOW}⚠ PARTIAL${NC}"
            ((PARTIAL_COUNT++))
            ;;
        CPU_START)
            echo -e "${YELLOW}⚠ CPU_START (no UART)${NC}"
            ((CPU_START_COUNT++))
            ;;
        CPU_RESET)
            echo -e "${RED}✗ CPU_RESET${NC}"
            ((CPU_RESET_COUNT++))
            ;;
        FAIL)
            echo -e "${RED}✗ FAIL${NC}"
            ((FAIL_COUNT++))
            ;;
        *)
            echo -e "${RED}✗ UNKNOWN${NC}"
            ((FAIL_COUNT++))
            ;;
    esac
done

echo ""
echo "Results:"
echo "  ✓ Pass:       $PASS_COUNT/7"
echo "  ⚠ Partial:    $PARTIAL_COUNT/7"
echo "  ⚠ CPU Start:  $CPU_START_COUNT/7"
echo "  ✗ CPU Reset:  $CPU_RESET_COUNT/7"
echo "  ✗ Fail:       $FAIL_COUNT/7"
echo ""

# =============================================================================
# Detailed Results
# =============================================================================

echo -e "${BLUE}========================================${NC}"
echo -e "${BLUE}  DETAILED RESULTS${NC}"
echo -e "${BLUE}========================================${NC}"
echo ""

for machine in virt raspi0 raspi1ap raspi2b raspi3ap raspi3b raspi4b; do
    echo -e "${YELLOW}$machine:${NC}"
    echo "${TEST_OUTPUTS[$machine]}"
    echo ""
done

# =============================================================================
# Analysis & Recommendations
# =============================================================================

echo -e "${BLUE}========================================${NC}"
echo -e "${BLUE}  ANALYSIS${NC}"
echo -e "${BLUE}========================================${NC}"
echo ""

if [ $PASS_COUNT -eq 0 ]; then
    echo -e "${RED}No platforms passed!${NC}"
    echo ""
    echo "Likely causes:"
    echo "  1. Bootloader hardcoded to wrong UART address for all platforms"
    echo "  2. Need hardware abstraction layer (hardware.c, hal.c)"
    echo ""
    echo "Next steps:"
    echo "  1. Check which platforms reached PC=0x80000 (CPU started)"
    echo "  2. Add platform detection code"
    echo "  3. Use correct UART addresses per platform:"
    echo "     - virt:       0x09000000"
    echo "     - raspi0/1:   0x20201000"
    echo "     - raspi2/3:   0x3F201000"
    echo "     - raspi4:     0xFE201000"
fi

if [ $CPU_START_COUNT -gt 0 ]; then
    echo -e "${YELLOW}$CPU_START_COUNT platforms reached entry point but no UART output${NC}"
    echo ""
    echo "This means:"
    echo "  - Boot sequence starts correctly"
    echo "  - CPU execution begins"
    echo "  - UART address is wrong for these platforms"
    echo ""
    echo "Fix: Update UART addresses in uart.c"
fi

if [ $CPU_RESET_COUNT -gt 0 ]; then
    echo -e "${RED}$CPU_RESET_COUNT platforms didn't start CPU execution${NC}"
    echo ""
    echo "This means:"
    echo "  - CPU reset occurred but didn't reach entry point"
    echo "  - Likely need GPU firmware (raspi* machines)"
    echo ""
    echo "Fix: These platforms require SD card images with firmware"
fi

echo ""
echo "All test results saved in: $RESULTS_DIR/"
echo ""
echo -e "${BLUE}========================================${NC}"
echo ""
