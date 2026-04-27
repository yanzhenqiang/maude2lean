inductive Exists (A : Type) (P : A -> Prop) : Prop where
| intro : forall (w : A) (h : P w), Exists A P

-- 辅助定义：从 Exists 提取 Prop 结论（绕过 rec.Exists motive 的 kernel BVar 偏移问题）
def exists_elim_prop (A : Type) (P : A -> Prop) (Q : Prop) (h : forall (w : A), P w -> Q) (e : Exists A P) : Q :=
  rec.Exists A P (fun _ => Q) h e

-- 选择公理：从 Exists 中提取 witness
axiom choice : forall (A : Type) (P : A -> Prop) (e : Exists A P), A
axiom choice_spec : forall (A : Type) (P : A -> Prop) (e : Exists A P), P (choice A P e)
