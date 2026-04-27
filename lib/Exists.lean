inductive Exists (A : Type) (P : A -> Prop) : Prop where
| intro : forall (w : A) (h : P w), Exists A P

-- Auxiliary definition: extract Prop conclusion from Exists (workaround for rec.Exists motive kernel BVar shift issue)
def exists_elim_prop (A : Type) (P : A -> Prop) (Q : Prop) (h : forall (w : A), P w -> Q) (e : Exists A P) : Q :=
  rec.Exists A P (fun _ => Q) h e

-- Axiom of choice: extract witness from Exists
axiom choice : forall (A : Type) (P : A -> Prop) (e : Exists A P), A
axiom choice_spec : forall (A : Type) (P : A -> Prop) (e : Exists A P), P (choice A P e)
