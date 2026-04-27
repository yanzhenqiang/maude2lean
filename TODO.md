# TODO

## Code Quality / Readability

- **Refactor `Goal.needs_cdecl_abstraction`**: The flag distinguishing function subgoals (need CDecl abstraction) from plain proof subgoals (don't need) is a workaround. A cleaner approach would be to track goal kind explicitly or redesign the mvar system so subgoals inherently know whether they represent function bodies or proof terms.
- **Reduce hardcoding in Rust**: Constructor names like `Eq.refl`, `Nat.zero`, `Nat.succ` are hardcoded in tactic.rs and repl_parser.rs. Consider a registry-driven approach where the kernel exposes constructor metadata so the parser/tactic engine doesn't need string constants.
- **Clean up `to_expr` namespace resolution**: The bare-name-to-namespaced fallback in `repl_parser.rs` works but could be more principled with a dedicated name-resolution pass.

## Known Issues

- **Match-based recursive definitions cause segfault in batch mode**: When `Nat.cic` or `Int.cic` use `match` for recursive definitions (`nat_add`, `nat_mul`, `int_add`), type-checking deeply nested proofs in downstream files (e.g., `NatProof.cic`) triggers a segfault. This appears to be a state contamination or stack-overflow issue in the type checker when processing match-desugared recursor expressions. Currently reverted to hand-written `rec.Nat`/`rec.Int` in those files.

## Future Mathematical Libraries

- **Euclidean Geometry Axiom System**: Define axioms for Euclidean geometry (points, lines, incidence, betweenness, congruence) following Hilbert or Tarski. Build toward proving classic theorems (e.g., sum of angles in a triangle).
  - **Status**: Initial framework complete in `lib/Geometry.cic`. Includes Hilbert-style axioms (I1-I3 incidence, O1-O4 order, C1-C5 congruence, Playfair parallel), basic definitions (collinear, segment, triangle, ray, midpoint, isosceles, equilateral), and sample theorems (between_implies_collinear, parallel_sym, parallel_through construction via choice).

## Visualization / UX

- **Penrose-like Diagram Generation**: Given geometric constructions or commutative diagrams stated in CIC, generate declarative diagrams (similar to [Penrose](https://penrose.cs.cmu.edu/)) from proof terms or definitions.
