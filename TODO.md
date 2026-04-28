# TODO

## Code Quality / Readability

- **Refactor `Goal.needs_cdecl_abstraction`**:
  - **Status**: DONE. Replaced `needs_cdecl_abstraction: bool` with `GoalKind` enum (`Proof` / `Function`).

- **Reduce hardcoding in Rust**:
  - **Status**: DONE. `Eq.refl` in `tactic.rs` uses `env.get_constructor`. Numeric literals use `ParsedExpr::NatLit(n)` with deferred expansion via `env.get_constructor`.

- **Clean up `to_expr` namespace resolution**:
  - **Status**: DONE. Extracted `resolve_name` function with 6-tier priority resolution. Added `Environment::resolve_constant_name`.

- **Extract universal expression formatter**:
  - **Status**: DONE. Created `src/format.rs` with shared `format_expr`. Supports infix operators (`+`, `-`, `*`, `/`, `=`, `<=`, `And`, `Or`, etc.), numeric literal detection (`succ^n zero` -> `n`), binder name tracking, FVar prettification. REPL, TUI, and CLI all use the shared formatter.

## Known Issues

- **Match-based recursive definitions cause segfault in batch mode**:
  - `desugar_match` now correctly replaces recursive calls with `ih` variables (the root cause was fixed).
  - However, using `match` for `nat_add`/`nat_mul` in `Nat.cic` still triggers a segfault when checking deeply nested proofs in downstream files (`NatProof.cic`). This appears to be a state contamination or stack-overflow issue in the type checker when processing match-desugared recursor expressions. Currently reverted to hand-written `rec.Nat` in `Nat.cic`. The fix in `repl_parser.rs` is preserved for future investigation.

## In Progress / Next Tasks

### 1. Euclidean Geometry Theorems
- **Status**: `lib/Geometry.cic` has Hilbert-style axioms (I1-I3 incidence, O1-O4 order, C1-C5 congruence, Playfair parallel), angle axioms (Hilbert Group III), SAS/ASA, and basic theorems (isosceles base angles). Midpoint uniqueness is temporarily an axiom pending SSS proof.
- **Blocker**: To prove SSS and midpoint uniqueness, we need additional congruence lemmas not yet in the system.
- **Next steps**:
  1. Prove SSS congruence criterion
  2. Convert midpoint_unique from axiom to theorem (needs SSS)
  3. Prove sum of angles in a triangle = 180 degrees (needs more angle lemmas)

### 2. Real Analysis Library
- **Goal**: Build real analysis on top of existing real number construction (Frac -> Real via Cauchy sequences).
- **Topics**:
  1. Real number properties (completeness [DONE in Complete.cic], Archimedean property, density of rationals)
  2. Sequence convergence definitions and basic theorems
  3. Function continuity definition and properties
  4. Function derivative definition
  5. Differential rules (chain rule, product rule, quotient rule)
  6. Riemann integral definition
  7. Fundamental Theorem of Calculus
  8. L'Hôpital's Rule
  9. Green's Formula (2D)
  10. Complex numbers (as pairs of reals)
  11. Cauchy's theorem for complex integration

### 3. Penrose-like Diagram Generation
- **Idea**: Given geometric constructions or commutative diagrams stated in CIC, generate declarative diagrams (similar to [Penrose](https://penrose.cs.cmu.edu/)) from proof terms or definitions.
- **Approach**:
  - Parse geometric definitions (`Point`, `Line`, `on_line`, `between`) from `lib/Geometry.cic`
  - Generate a declarative diagram specification (e.g., constraint-based layout)
  - Output to a simple format (SVG, TikZ, or ASCII art) that can be rendered
  - Could start with ASCII art for immediate feedback, then upgrade to SVG

## Completed (Recently)

- [x] TUI: show tactic goals on empty/comment lines inside `by` blocks (Lean-like infoview behavior)
- [x] Fix binder-aware MVar substitution in `TacticEngine` (convert FVars to BVars during `build_proof`)
- [x] Rewrite `lib/Complete.cic` proofs to `by` tactic style (`cauchy_complete`, `const_seq_converges`)
- [x] Convert simple term-style proofs to `by` style (`collinear_perm`, `frac_abs_zero`, `frac_lt_zero_one`, etc.)
- [x] Fix match-based recursive definitions (replace recursive calls with ih in minor premises)
- [x] Extract and enhance universal expression formatter (`src/format.rs`)
- [x] Clean up debug output `.txt` files
- [x] Remove duplicate match-based Nat library files
- [x] Clean up temporary `lib/test.cic` file
- [x] Complete Euclidean geometry axioms and theorems (angle axioms, SAS/ASA, isosceles base angles)
- [x] Fix inline `--` comment parsing inside expressions (`skip_whitespace` now skips comments)
