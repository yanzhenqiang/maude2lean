-- 等式归纳族
-- Eq A a b 表示在类型 A 中 a = b

inductive Eq (A : Type) (a : A) : A -> Prop where
| refl : Eq A a a

-- 等式替换原理（rewrite）
def eq_subst (A : Type) (a : A) (b : A) (P : A -> Prop) (h : Eq A a b) (pa : P a) : P b :=
  rec.Eq A a (fun x : A => fun _ : Eq A a x => P x) pa b h
