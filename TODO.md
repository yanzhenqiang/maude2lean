# TODO

## Code Quality / Readability

- **Refactor `Goal.needs_cdecl_abstraction`**: The flag distinguishing function subgoals (need CDecl abstraction) from plain proof subgoals (don't need) is a workaround. A cleaner approach would be to track goal kind explicitly or redesign the mvar system so subgoals inherently know whether they represent function bodies or proof terms.
- **Reduce hardcoding in Rust**: Constructor names like `Eq.refl`, `Nat.zero`, `Nat.succ` are hardcoded in tactic.rs and repl_parser.rs. Consider a registry-driven approach where the kernel exposes constructor metadata so the parser/tactic engine doesn't need string constants.
- **Clean up `to_expr` namespace resolution**: The bare-name-to-namespaced fallback in `repl_parser.rs` works but could be more principled with a dedicated name-resolution pass.

## Future Mathematical Libraries

- **Euclidean Geometry Axiom System**: Define axioms for Euclidean geometry (points, lines, incidence, betweenness, congruence) following Hilbert or Tarski. Build toward proving classic theorems (e.g., sum of angles in a triangle).

## Visualization / UX

- **Penrose-like Diagram Generation**: Given geometric constructions or commutative diagrams stated in CIC, generate declarative diagrams (similar to [Penrose](https://penrose.cs.cmu.edu/)) from proof terms or definitions.
