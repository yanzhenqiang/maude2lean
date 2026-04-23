#!/bin/bash
# TUI viewer shortcut for lean-cauchy-kernel
# Usage: ./tui.sh <target.lean>

DEPS="Nat.lean Eq.lean Order.lean True.lean Int.lean IntOrder.lean Frac.lean Exists.lean WellFounded.lean NatProof.lean FracArith.lean Cauchy.lean Real.lean"

cargo run -- tui "$1" $DEPS
