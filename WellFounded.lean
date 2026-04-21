-- Well-Founded Recursion 基础定义
-- 对应 Lean 4 的 WellFounded 内核扩展

-- Acc: Accessibility predicate
inductive Acc (A : Type) (R : A -> A -> Prop) (a : A) : Prop where
| acc_intro : (forall (b : A), R b a -> Acc A R b) -> Acc A R a

-- WellFounded: 所有元素都可访问
inductive WellFounded (A : Type) (R : A -> A -> Prop) : Prop where
| wf_intro : (forall (a : A), Acc A R a) -> WellFounded A R

-- WellFounded.fix: 通过良基关系定义递归函数
axiom wellFounded_fix :
  forall (A : Type),
  forall (C : A -> Type),
  forall (R : A -> A -> Prop),
  forall (hwf : WellFounded A R),
  forall (F : forall (x : A), (forall (y : A), R y x -> C y) -> C x),
  forall (x : A), C x
