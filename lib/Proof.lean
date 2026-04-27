theorem const_nat : forall (n : Nat), Nat -> Nat :=
  fun n : Nat => fun m : Nat => n

theorem id_nat : forall (n : Nat), Nat -> Nat :=
  fun n : Nat => fun m : Nat => m
