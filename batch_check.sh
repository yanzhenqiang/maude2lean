#!/bin/bash
# Batch check all .lean files in dependency order

BIN="./target/debug/lean-cauchy-kernel"

check_file() {
    local file="$1"
    echo "========================================"
    echo "Checking: $file"
    echo "========================================"
    {
        echo ":load $file"
        echo ":quit"
    } | timeout 10 $BIN repl 2>&1 | grep -E "(Error|error|Loaded|Proof does not match|Type mismatch|Parse error)" || true
    echo ""
}

# Check individual files in dependency order
check_file "True.lean"
check_file "Order.lean"
check_file "Nat.lean"
check_file "Eq.lean"
check_file "NatProof.lean"
check_file "Int.lean"
check_file "IntOrder.lean"
check_file "Frac.lean"
check_file "Cauchy.lean"
check_file "FracArith.lean"
check_file "Real.lean"
check_file "Complete.lean"

echo "========================================"
echo "All files checked"
echo "========================================"
