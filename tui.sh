#!/bin/bash
# TUI viewer shortcut for lean-cauchy-kernel
# Usage: ./tui.sh <target.cic>

DEPS="Nat.cic Eq.cic Order.cic True.cic Int.cic IntOrder.cic Frac.cic Exists.cic WellFounded.cic NatProof.cic FracArith.cic Cauchy.cic Real.cic"

cargo run -- tui "$1" $DEPS
