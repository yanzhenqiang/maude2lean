-- 只测试中间引理
inductive Nat where
| zero : Nat
| succ : Nat -> Nat

inductive Bool where
| false : Bool
| true : Bool

def not (b : Bool) : Bool :=
  match b : Bool with | false => true | true => false

inductive List (A : Type) where
| nil : List A
| cons : A -> List A -> List A

def list_length (A : Type) (xs : List A) : Nat :=
  rec.List A (fun _ => Nat) zero (fun x xs ih => succ ih) xs

def list_filter (A : Type) (p : A -> Bool) (xs : List A) : List A :=
  rec.List A (fun _ => List A) (nil A) (fun x xs ih => match p x : List A with | true => cons A x ih | false => ih) xs

def list_append (A : Type) (xs ys : List A) : List A :=
  rec.List A (fun _ => List A) ys (fun x xs ih => cons A x ih) xs

def nat_gt (m n : Nat) : Bool :=
  rec.Nat (fun _ => Nat -> Bool)
    (fun n => false)
    (fun m' => \ih : Nat -> Bool . \n : Nat . rec.Nat (fun _ => Bool) true (fun n' ih2 => ih n') n)
    m
    n

def nat_le (m n : Nat) : Bool := not (nat_gt m n)

def nat_eq (m n : Nat) : Bool :=
  rec.Nat (fun _ => Nat -> Bool)
    (fun n => rec.Nat (fun _ => Bool) true (fun n' ih => false) n)
    (fun m' => \ih : Nat -> Bool . \n : Nat . rec.Nat (fun _ => Bool) false (fun n' ih2 => ih n') n)
    m
    n

def nat_add (m n : Nat) : Nat :=
  rec.Nat (fun _ => Nat) n (fun n' ih => succ ih) m

inductive Eq : forall (A : Type) (a : A) (b : A), Prop where
| refl : forall (A : Type) (a : A), Eq A a a

def eq_subst (A : Type) (a : A) (b : A) (P : A -> Prop) (h : Eq A a b) (pa : P a) : P b :=
  rec.Eq A a (fun x : A => fun _ : Eq A a x => P x) pa b h

def eq_sym (A : Type) (a : A) (b : A) (h : Eq A a b) : Eq A b a :=
  eq_subst A a b (fun y : A => Eq A y a) h (refl A a)

def list_count (A : Type) (eq : A -> A -> Bool) (x : A) (xs : List A) : Nat :=
  rec.List A (fun _ => Nat)
    zero
    (fun y ys ih => match eq x y : Nat with | true => succ ih | false => ih)
    xs

-- nat_add 引理
theorem nat_add_zero_r (m : Nat) : Eq Nat (nat_add m zero) m :=
  refl Nat m

theorem nat_add_succ_r (m n : Nat) : Eq Nat (nat_add m (succ n)) (succ (nat_add m n)) :=
  refl Nat (succ (nat_add m n))

theorem nat_add_succ_l (m n : Nat) : Eq Nat (nat_add (succ m) n) (succ (nat_add m n)) :=
  rec.Nat (fun n => Eq Nat (nat_add (succ m) n) (succ (nat_add m n)))
    (refl Nat (succ m))
    (fun n' ih => eq_subst Nat (nat_add (succ m) n') (succ (nat_add m n'))
      (fun y => Eq Nat (succ (nat_add (succ m) n')) (succ y))
      ih
      (refl Nat (succ (nat_add (succ m) n'))))
    n

theorem nat_add_comm (m n : Nat) : Eq Nat (nat_add m n) (nat_add n m) :=
  rec.Nat (fun x => Eq Nat (nat_add x n) (nat_add n x))
    (eq_sym Nat (nat_add n zero) n (nat_add_zero_r n))
    (fun m' ih => eq_subst Nat (nat_add n m') (nat_add m' n)
      (fun y => Eq Nat (succ y) (nat_add n (succ m')))
      (eq_sym Nat (nat_add m' n) (nat_add n m') ih)
      (eq_sym Nat (nat_add n (succ m')) (succ (nat_add n m')) (nat_add_succ_r n m')))
    m

-- count_append
theorem count_append (x : Nat) (xs ys : List Nat)
  : Eq Nat (list_count Nat nat_eq x (list_append Nat xs ys))
           (nat_add (list_count Nat nat_eq x xs) (list_count Nat nat_eq x ys)) :=
  rec.List Nat (fun zs => Eq Nat (list_count Nat nat_eq x (list_append Nat zs ys))
                                 (nat_add (list_count Nat nat_eq x zs) (list_count Nat nat_eq x ys)))
    (refl Nat (list_count Nat nat_eq x ys))
    (fun h t ih =>
      let a := list_count Nat nat_eq x t in
      let b := list_count Nat nat_eq x ys in
      rec.Bool (fun b' => Eq Nat
        (match b' : Nat with | true => succ (list_count Nat nat_eq x (list_append Nat t ys)) | false => list_count Nat nat_eq x (list_append Nat t ys))
        (nat_add (match b' : Nat with | true => succ a | false => a) b))
        (eq_subst Nat (nat_add (succ a) b) (succ (nat_add a b))
          (fun y => Eq Nat (succ (list_count Nat nat_eq x (list_append Nat t ys))) (succ y))
          (eq_sym Nat (succ (nat_add a b)) (nat_add (succ a) b) (nat_add_succ_l a b))
          (eq_subst Nat (list_count Nat nat_eq x (list_append Nat t ys)) (nat_add a b)
            (fun y => Eq Nat (succ (list_count Nat nat_eq x (list_append Nat t ys))) (succ y))
            ih
            (refl Nat (succ (list_count Nat nat_eq x (list_append Nat t ys))))))
        ih
        (nat_eq x h))
    xs

-- count_filter_partition
theorem count_filter_partition (p : Nat -> Bool) (x : Nat) (xs : List Nat)
  : Eq Nat (list_count Nat nat_eq x xs)
           (nat_add (list_count Nat nat_eq x (list_filter Nat p xs))
                    (list_count Nat nat_eq x (list_filter Nat (fun y : Nat => not (p y)) xs))) :=
  rec.List Nat (fun zs => Eq Nat (list_count Nat nat_eq x zs)
                                 (nat_add (list_count Nat nat_eq x (list_filter Nat p zs))
                                          (list_count Nat nat_eq x (list_filter Nat (fun y : Nat => not (p y)) zs))))
    (eq_subst Nat zero (nat_add zero zero)
      (fun y => Eq Nat zero y)
      (eq_sym Nat (nat_add zero zero) zero (nat_add_zero_r zero))
      (refl Nat zero))
    (fun h t ih =>
      let a := list_count Nat nat_eq x (list_filter Nat p t) in
      let b := list_count Nat nat_eq x (list_filter Nat (fun y : Nat => not (p y)) t) in
      rec.Bool (fun b' => forall (h_eq : Eq Bool (p h) b'),
        Eq Nat (match nat_eq x h : Nat with | true => succ (nat_add a b) | false => nat_add a b)
               (nat_add (match b' : Nat with
                         | true => match nat_eq x h : Nat with | true => succ a | false => a
                         | false => match nat_eq x h : Nat with | true => succ b | false => b)
                        (nat_add a b)))
        (fun h_true : Eq Bool (p h) true =>
          rec.Bool (fun b2 => Eq Nat (match b2 : Nat with | true => succ (nat_add a b) | false => nat_add a b)
                                     (match b2 : Nat with | true => succ (nat_add a b) | false => nat_add a b))
            (refl Nat (succ (nat_add a b)))
            (refl Nat (nat_add a b))
            (nat_eq x h))
        (fun h_false : Eq Bool (p h) false =>
          rec.Bool (fun b2 => Eq Nat (match b2 : Nat with | true => succ (nat_add a b) | false => nat_add a b)
                                     (match b2 : Nat with | true => nat_add (succ b) (nat_add a b) | false => nat_add b (nat_add a b)))
            (eq_subst Nat (nat_add b (nat_add a b)) (nat_add (nat_add a b) b)
              (fun y => Eq Nat (nat_add a b) y)
              (nat_add_comm b (nat_add a b))
              (refl Nat (nat_add a b)))
            (eq_subst Nat (succ (nat_add a b)) (nat_add (succ b) (nat_add a b))
              (fun y => Eq Nat (succ (nat_add a b)) y)
              (eq_sym Nat (nat_add (succ b) (nat_add a b)) (succ (nat_add a b)) (nat_add_succ_l b (nat_add a b)))
              (refl Nat (succ (nat_add a b))))
            (nat_eq x h))
        (p h)
        (refl Bool (p h)))
    xs
