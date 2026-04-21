#!/bin/bash
# Check all .lean files in dependency order within a single REPL session

BIN="./target/debug/lean-cauchy-kernel"

{
    echo ":load True.lean"
    echo ":load Order.lean"
    echo ":load Nat.lean"
    echo ":load Eq.lean"
    echo ":load NatProof.lean"
    echo ":load Int.lean"
    echo ":load IntOrder.lean"
    echo ":load Frac.lean"
    echo ":load Cauchy.lean"
    echo ":load FracArith.lean"
    echo ":load Real.lean"
    echo ":load Complete.lean"
    echo ":quit"
} | timeout 30 $BIN repl 2>&1
