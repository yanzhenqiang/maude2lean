# tinycic

A minimal dependently-typed proof kernel in Rust, implementing a Lean 4-style CIC (Calculus of Inductive Constructions) with proof irrelevance, quotient types, and a lightweight tactic engine.

## Goals

Construct real numbers from Cauchy sequences and prove their completeness, all within a formally verified kernel:

> **is_cauchy a -> exists L, seq_converges_to a L**

## Architecture

```
Frontend: CIC Parser + REPL + TUI
- Recursive-descent parser
- inductive / def / theorem / axiom / structure / match
- Infix operators, forall / exists, lightweight tactics

Kernel: Dependent Type Theory
- Expr AST (de Bruijn indices, universe levels)
- Type checker (WHNF, is_def_eq, infer, check)
- Environment (inductive decls, auto-generated recursors)
- Proof Irrelevance + Quotient Types + MVar Unification
```

### Source Files (`src/`)

| File | Purpose |
|------|---------|
| `main.rs` | CLI entry. Subcommands: `lean-check`, `repl`, `check-files <file>...`, `tui <target> [deps...]` |
| `lib.rs` | Library entry, re-exports all public modules |
| `expr.rs` | Expression AST: BVar, FVar, MVar, Const, App, Lambda, Pi, Let. de Bruijn operations |
| `declaration.rs` | Declarations: Axiom, Definition, Theorem, Inductive, Quot, and value structs |
| `environment.rs` | Global `Environment`, auto recursor/constructor registration, nested inductive helpers |
| `local_ctx.rs` | Local context `LocalCtx`, CDecl/LDecl management, BVar <-> FVar conversion |
| `type_checker.rs` | Type checker: `infer`, `check`, `whnf`, `nf`, `is_def_eq`. Universe constraints, let-reduction, MVars |
| `tactic.rs` | Tactic engine: `intro`, `exact`, `apply`, `rw`, `rfl`, `assumption`, `induction`, `have` |
| `repl.rs` | Interactive REPL: `:load`, `:def`, `:theorem`, `:inductive`, `:infer`, `:reduce`, `:nf` |
| `repl_parser.rs` | Lean-style parser: expressions, top-level declarations, infix operators, calc blocks |
| `tui.rs` | `crossterm`-based TUI for viewing goals, local context, and hypotheses |
| `test_auto_rec.rs` | Unit tests for auto recursor generation |

### Standard Library / Examples (`lib/`)

| File | Content |
|------|---------|
| `Nat.cic` | `Nat` (zero/succ), `nat_add`, `nat_mul`, `nat_sub` |
| `Eq.cic` | `Eq A a b`, `refl`, `eq_sym`, `eq_subst` |
| `Order.cic` | `le`, `le_zero`, `le_succ`, `le_refl`, `le_trans` |
| `logic.cic` | `True`, `False`, `Or`, `Not` |
| `Int.cic` | `Int` (ofNat/negSucc), arithmetic, recursor |
| `IntOrder.cic` | Integer ordering relations |
| `Frac.cic` | `Frac` (num/den), arithmetic, `frac_lt`, `frac_inv` |
| `FracArith.cic` | Fraction lemmas: commutativity, `frac_dist_self`, Cauchy distance |
| `NatProof.cic` | `nat_add_comm`, `nat_mul_comm`, `nat_add_assoc` |
| `Real.cic` | `Real` as quotient of Cauchy sequences |
| `Cauchy.cic` | `is_cauchy`, `cauchy_equiv` |
| `Complete.cic` | `cauchy_complete`, `limit_seq`, `limit_real` |
| `Algebra.cic` | Algebraic structure examples |
| `Exists.cic` | `Exists`, `choice`, `choice_spec` |
| `WellFounded.cic` | `Acc`, `WellFounded`, `wellFounded_fix` |
| `solve.cic` | Solve/theorem examples: basic tactics, derivations, quadratic formula, fraction algebra |
| `Decimal.cic` | Decimal number system, quicksort, sorting proofs |
| `decimal_data.cic` | Test data for decimal quicksort |
| `decimal_quicksort.cic` | Permutation proofs for quicksort correctness |
| `Proof.cic` | Proof examples |

### Test Files

| File | Purpose |
|------|---------|
| `test.cic` | Basic REPL loading test |
| `test_rw.cic` / `test_rw2.cic` | Chained / reverse `rw` tactic tests |
| `test_notation.cic` | Custom notation test |
| `test_induction.cic` | Induction tactic test |
| `test_nat*.cic` | Natural number tactic tests |

## Build & Run

```bash
# Build
cargo build --release

# Kernel demo (type checking, WHNF, reduction, defeq)
cargo run -- lean-check

# Interactive REPL
cargo run -- repl

# Batch check .cic files
cargo run -- check-files lib/Nat.cic lib/Eq.cic lib/NatProof.cic

# TUI viewer
cargo run -- tui lib/Decimal.cic lib/Nat.cic lib/Order.cic
```

## REPL Commands

```
:load <file.cic>              Load a .cic file (supports import)
:def <name> : <ty> := <val>    Add a definition
:theorem <name> : <ty> := <pf> Add a theorem (supports by-tactic blocks)
:inductive <name> | <c>:<t>    Add an inductive type
:infer <expr>                  Infer expression type
:reduce <expr>                 Weak head normal form
:nf <expr>                     Full normal form
:defeq <e1> = <e2>             Check definitional equality
:solve <name> : <ty> := <expr> Solve mode with metavariables
:env                           Show current environment
:help                          Show help
:quit                          Exit
```

## Tactic Examples

```cic
theorem test_rw_chain : forall (a b c d : Nat), Eq Nat a b -> Eq Nat b c -> Eq Nat c d -> Eq Nat a d := by
  intro a b c d h1 h2 h3
  rw [h1, h2, h3]
  rfl

theorem test_induction : forall (n : Nat), Eq Nat n n := by
  intro n
  induction n
  rfl
  intro n
  intro ih
  rfl
```

## Mathematical Construction

Formalization chain from naturals to reals:

```
Nat -> Order -> Int -> IntOrder -> Frac -> FracArith -> Cauchy -> Real -> Complete
```

- `Frac = Int x Nat` represents `num/(den+1)`, denominator always positive
- `Real` constructed via quotient type; `seq_converges_to` defined with `Quot.ind`
- `is_cauchy` witness extraction via `choice` axiom

## Kernel Coverage

| Feature | Status |
|---------|--------|
| CIC + Proof Irrelevance + Quotient | Complete |
| Inductive types + Auto recursors | Single + mutual + nested (auto-encoded) |
| Universe constraint solving + MVar unification | Complete |
| Tactics (intro/exact/apply/rw/induction/have/rfl/assumption) | Complete |
| Well-founded recursion | `Acc` + `WellFounded` + `wellFounded_fix` axiom |
| Elaborator (implicit args, type classes) | Not implemented |
| Pattern match compiler | Simple constructor discrimination only |
| Compiler backend | Not implemented |

## Key Bug Fixes

| Bug | Fix |
|-----|-----|
| `mk_inductive_app` param order | Fixed BVar offset for `rec.Exists` motive |
| `is_def_eq` Pi/Lambda fresh FVar unregistered | Added `push_bvar` + `mk_local_decl` |
| `is_prop_type` missed constant Prop | Fallback to `infer(e)` check |
| `is_def_eq` incorrect proof irrelevance | Only equal when definitionally equal |
| FVar name collisions in induction | Unique internal names in `LocalCtx` |

## Dependencies

```toml
[dependencies]
crossterm = "0.29.0"   # TUI only
indexmap = "2.2"       # Ordered environment
```

Both are minimal and actively maintained. `crossterm` is only used by `tui.rs`.
