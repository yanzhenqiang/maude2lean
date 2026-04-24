solve test_refl : Eq Nat zero zero := by refl

solve test_exact : Eq Nat zero zero := by exact refl Nat zero

solve test_intro : forall (n : Nat), Eq Nat n n := by intro n; refl
