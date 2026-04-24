# TTobs Kernel Design

Based on Pujet & Tabareau, *Observational Equality: Now for Good*, POPL 2022.

## 1. Philosophy

The kernel must be **minimal**. Only mechanisms that increase the expressive power of the theory live in the core. Everything else — general inductive types, quotients, identity types, sigma types, boxed types — lives in the outer/frontend layer.

Core expressive-power mechanisms:
- Two sort hierarchies: proof-relevant `𝒰 i` and proof-irrelevant `Ω i`
- Observational equality `t ~_A u` with type-directed reduction
- Cast `cast(A, B, e, t)` with type-directed reduction
- Proof irrelevance (any two terms of `Ω` type are convertible)
- Cumulativity across sorts

## 2. Core Syntax

```
t, A, B ::= x                      -- variable
         |  λ(x : A). t            -- lambda
         |  t u                    -- application
         |  Π(x : A). B            -- product
         |  𝒰 i                    -- proof-relevant universe
         |  Ω i                    -- proof-irrelevant universe
         |  t ~_A u               -- observational equality
         |  cast(A, B, e, t)      -- cast
         |  c[A₁,...,Aₙ]          -- global constant (with universe levels)
```

No `let`, no pattern matching, no inductive types, no recursors, no fixpoints in the core. These are all outer-layer features that desugar into the core.

## 3. Sorts and Cumulativity

```
𝒰 i  :  𝒰 (i+1)        for i ≥ 0
Ω i  :  𝒰 (i+1)        for i ≥ 0
```

Cumulativity (subtyping):
```
𝒰 i ≤ 𝒰 j     when i ≤ j
Ω i ≤ Ω j     when i ≤ j
Ω i ≤ 𝒰 j     when i ≤ j
```

The inclusion `Ω i ≤ 𝒰 j` means proof-irrelevant types can be used in proof-relevant contexts, but not vice versa.

## 4. Observational Equality

Observational equality `t ~_A u` is **not** an inductive type. It has no constructors. Instead, it reduces by pattern-matching on the WHNF of `A`.

### Eq-* reduction rules (Figure 4 from paper):

**Eq-𝒰:**
```
A ~_𝒰ᵢ B   ▷   A =_Ωᵢ B
```
Equality at a universe is equivalence of types (as a proposition in `Ω`).

**Eq-Ω:**
```
p ~_Ωᵢ q   ▷   p →_Ωᵢ q ∧ q →_Ωᵢ p
```
Equality of proofs is logical equivalence.

**Eq-Π:**
```
f ~_(Π(x:A).B) g   ▷   Π(x:A). f x ~_B g x
```
Function extensionality is definitional.

**Eq-η (eta for equality):**
```
refl A t : t ~_A t   ▷   canonical proof (any term of the right type)
```
Proofs of reflexivity are definitionally equal to any proof of the equality.

## 5. Cast

`cast(A, B, e, t)` coerces `t : A` to type `B`, given `e : A ~_Ωᵢ B`.

### Cast-* reduction rules:

**Cast-𝒰:**
```
cast(𝒰ᵢ, 𝒰ᵢ, e, A)   ▷   A
```

**Cast-Ω:**
```
cast(Ωᵢ, Ωᵢ, e, p)   ▷   p
```

**Cast-Π:**
```
cast(Π(x:A).B, Π(x:A').B', e, f)   ▷
  λ(x:A'). cast(B[x'/x], B', e x', f (cast(A', A, sym e, x')))
```
where `x' = cast(A', A, sym e, x)` and `sym e : A' ~ A`.

This is the key rule: casts commute with function types, and function casts become lambda wrappers that cast arguments and results appropriately.

## 6. Conversion Rules (Figure 3)

### β-reduction:
```
(λx.t) u = t[u/x]
```

### η-expansion:
```
t = λx. t x    when t : Π(x:A).B
```

### Proof irrelevance:
```
t = u          when Γ ⊢ t : A and Γ ⊢ u : A and A : Ω i
```
Any two proofs of the same proposition are definitionally equal.

### Congruence:
Standard congruence rules for all term formers.

## 7. WHNF and Neutral Forms (Figure 5)

A term is in **Weak Head Normal Form (WHNF)** if it is one of:
- `λ(x:A).t`
- `Π(x:A).B`
- `𝒰 i` or `Ω i`
- `t ~_A u` where `t` and `u` are neutral
- `cast(A, B, e, t)` where `t` is neutral and A, B are in WHNF
- A **neutral** term

A term is **neutral** if it is:
- A variable `x`
- A stuck application `t u` where `t` is neutral and not a lambda
- A stuck cast `cast(A, B, e, t)` where `t` is neutral and the cast-* rule does not apply

The key insight: `cast` and `~` are **stuck** (neutral) when their arguments are neutral, but reduce when enough type information is available.

## 8. Type Checking Algorithm

### Conversion check (is_def_eq):
```
1. Reduce both sides to WHNF.
2. If both are neutral and syntactically equal, return true.
3. If both are the same constructor (λ/Π/𝒰/Ω), recurse on subterms.
4. If one is η-expandable (function type), η-expand and retry.
5. If both are in Ω (proof-irrelevant), return true immediately.
6. If both are casts with convertible proofs, reduce the cast and retry.
7. Otherwise, false.
```

### Type inference:
```
infer(x)          = Γ(x)
infer(λx:A.t)     = Π(x:A).infer(t)   (with A : 𝒰ᵢ or Ωᵢ)
infer(t u)        = B[u/x]  where infer(t) = Π(x:A).B and check(u, A)
infer(Π(x:A).B)   = 𝒰_{max(i,j)}  where A : 𝒰ᵢ/Ωᵢ and B : 𝒰ⱼ/Ωⱼ
infer(𝒰 i)        = 𝒰 (i+1)
infer(Ω i)        = 𝒰 (i+1)
infer(t ~_A u)    = Ω i  where A : 𝒰ᵢ/Ωᵢ and check(t, A) and check(u, A)
infer(cast(A,B,e,t)) = B  where check(e, A ~_Ωᵢ B) and check(t, A)
```

## 9. Core vs Outer Layer Boundary

### In the core (`src/lean/`):
- `expr.rs`: Core syntax (λ, App, Π, 𝒰, Ω, ~, cast, constants)
- `type_checker.rs`: WHNF reduction, conversion, inference
- `environment.rs`: Global constants (axioms, definitions)
- `declaration.rs`: Constant declarations
- `name.rs`, `level.rs`: Names and universe levels

### In the outer layer (future):
- Parser for surface syntax (inductive, let, pattern matching)
- Elaborator: desugar surface syntax to core
- Inductive types: compiled to axioms + recursors
- `Σ` types: encoded as inductive or defined directly
- `Id` types: defined using observational equality
- Quotients: defined using propositional extensionality
- `Box` types: promotion between `𝒰` and `Ω`
- Tactics and proof automation
- TUI (can be rebuilt on top of the new kernel)

## 10. Why This is Simpler

Compared to the current Lean-like kernel:
- **No inductive type generation**: No recursor/constructor/computation rule synthesis.
- **No pattern matching**: All elimination is through `cast` and `~`.
- **Function extensionality is definitional**: No axioms needed.
- **UIP is definitional**: Proof irrelevance handles it.
- **Propositional extensionality is definitional**: Eq-Ω rule.
- **Univalence-adjacent**: Type equivalence (A ~_𝒰 B) gives casts between types.

## 11. File Structure Plan

```
src/lean/
  mod.rs              -- module exports
  name.rs             -- Name (unchanged)
  level.rs            -- Level (unchanged)
  expr.rs             -- Expr: BVar, Const, App, Lambda, Pi, Sort(U/Omega), Eq, Cast
  environment.rs      -- Environment: map Name -> Declaration
  declaration.rs      -- Declaration: Axiom, Definition (no Inductive in core)
  type_checker.rs     -- TypeChecker: infer, check, whnf, is_def_eq
  local_ctx.rs        -- LocalCtx (unchanged)
  repl.rs             -- REPL for core syntax (simplified)
  repl_parser.rs      -- Parser for core syntax

src/main.rs           -- Commands: check, repl, etc.

ott.md                -- This document
```

## 12. Implementation Order

1. Rewrite `expr.rs` with new syntax (keep old for reference, or branch)
2. Rewrite `type_checker.rs` with WHNF + Eq-* + Cast-* rules
3. Simplify `declaration.rs` / `environment.rs` (remove inductive)
4. Update parser for core syntax
5. Update REPL
6. Add basic tests demonstrating:
   - Function extensionality is definitional
   - Proof irrelevance
   - Cast reduction
   - Cumulativity

## 13. Key Invariants

- Every well-typed term has a unique WHNF (up to proof irrelevance).
- `cast` is transparent: `cast(A, B, e, t)` reduces to `t` when `A` and `B` are definitionally equal.
- Observational equality is proof-irrelevant: any two proofs `p, q : t ~_A u` are convertible.
- No `Eq` type in the core — the surface `Id` type will be defined as `t ~_A u` in the outer layer.
