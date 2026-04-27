-- Well-Founded Recursion basics
-- Corresponds to Lean 4's WellFounded kernel extension

-- Acc: Accessibility predicate
inductive Acc (A : Type) (R : A -> A -> Prop) (a : A) : Prop where
| acc_intro : (forall (b : A), R b a -> Acc A R b) -> Acc A R a

-- WellFounded: all elements are accessible
inductive WellFounded (A : Type) (R : A -> A -> Prop) : Prop where
| wf_intro : (forall (a : A), Acc A R a) -> WellFounded A R

-- WellFounded.fix: define recursive functions via well-founded relations
axiom wellFounded_fix :
  forall (A : Type),
  forall (C : A -> Type),
  forall (R : A -> A -> Prop),
  forall (hwf : WellFounded A R),
  forall (F : forall (x : A), (forall (y : A), R y x -> C y) -> C x),
  forall (x : A), C x
