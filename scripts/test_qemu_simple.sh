#!/bin/bash
# Simple QEMU Test Script (compatible with macOS bash 3.x)

# Test configuration
TEST_DURATION=5
RESULTS_DIR="qemu_test_results"
mkdir -p "$RESULTS_DIR"

echo "========================================"
echo "  QEMU ARM Platform Test Suite"
echo "========================================"
echo ""

# Check bootloader
if [ ! -f "bootloader.bin" ]; then
    echo "Error: bootloader.bin not found"
    exit 1
fi

echo "Bootloader: bootloader.bin ($(stat -f%z bootloader.bin 2>/dev/null || stat -c%s bootloader.bin) bytes)"
echo ""

# Test function
test_target() {
    local MACHINE=$1
    local CPU=$2
    local MEM=$3

    echo "----------------------------------------"
    echo "Testing: $MACHINE"
    echo "CPU: $CPU, Memory: $MEM"
    echo "----------------------------------------"

    local OUT="$RESULTS_DIR/${MACHINE}_output.log"
    local DBG="$RESULTS_DIR/${MACHINE}_debug.log"

    # Run QEMU
    qemu-system-aarch64 -M "$MACHINE" -cpu "$CPU" -m "$MEM" \
        -kernel bootloader.bin -nographic \
        -d guest_errors,cpu_reset -D "$DBG" \
        > "$OUT" 2>&1 &

    local PID=$!
    sleep $TEST_DURATION
    kill $PID 2>/dev/null
    wait $PID 2>/dev/null

    # Check results
    if grep -q "Minimal ARM Bootloader" "$OUT"; then
        echo "✓ PASS - UART output detected"
    elif grep -q "========" "$OUT"; then
        echo "⚠ PARTIAL - Some output"
    elif grep -q "PC=0000000000080000" "$DBG"; then
        echo "⚠ CPU_START - No UART output"
    elif grep -q "CPU Reset" "$DBG"; then
        echo "✗ CPU_RESET - Didn't start"
    else
        echo "✗ FAIL - No activity"
    fi

    echo "First 3 lines of output:"
    head -3 "$OUT" 2>/dev/null || echo "(no output)"
    echo ""
}

# Run tests
test_target "virt" "cortex-a72" "1G"
test_target "raspi0" "arm1176" "512M"
test_target "raspi1ap" "arm1176" "512M"
test_target "raspi2b" "cortex-a7" "1G"
test_target "raspi3ap" "cortex-a53" "512M"
test_target "raspi3b" "cortex-a53" "1G"
test_target "raspi4b" "cortex-a72" "4G"

echo "========================================"
echo "Tests complete. Results in: $RESULTS_DIR/"
echo "========================================"
