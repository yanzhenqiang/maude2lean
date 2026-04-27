inductive Eq : forall (A : Type) (a : A) (b : A), Prop where
| refl : forall (A : Type) (a : A), Eq A a a

def eq_subst (A : Type) (a : A) (b : A) (P : A -> Prop) (h : Eq A a b) (pa : P a) : P b :=
  rec.Eq A a (fun x : A => fun _ : Eq A a x => P x) pa b h

def eq_sym (A : Type) (a : A) (b : A) (h : Eq A a b) : Eq A b a :=
  eq_subst A a b (fun y : A => Eq A y a) h (refl A a)
