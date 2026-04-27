

def list_count (A : Type) (eq : A -> A -> Bool) (x : A) (xs : List A) : Nat :=
  rec.List A (fun _ => Nat)
    zero
    (fun y ys ih => match eq x y : Nat with | true => succ ih | false => ih)
    xs


def NatPerm (xs ys : List Nat) : Prop :=
  forall (x : Nat), Eq Nat (list_count Nat nat_eq x xs) (list_count Nat nat_eq x ys)


theorem count_nil (x : Nat) : Eq Nat (list_count Nat nat_eq x (nil Nat)) zero :=
  refl Nat zero

def count_cons_eq (x : Nat) (xs : List Nat)
  : Eq Nat (list_count Nat nat_eq x (cons Nat x xs)) (succ (list_count Nat nat_eq x xs)) :=
  refl Nat (succ (list_count Nat nat_eq x xs))

def count_cons_neq (x y : Nat) (xs : List Nat) (h : Eq Bool (nat_eq x y) false)
  : Eq Nat (list_count Nat nat_eq x (cons Nat y xs)) (list_count Nat nat_eq x xs) :=
  refl Nat (list_count Nat nat_eq x xs)


theorem nat_add_zero_r (m : Nat) : Eq Nat (nat_add m zero) m :=
  refl Nat m

theorem nat_add_succ_r (m n : Nat) : Eq Nat (nat_add m (succ n)) (succ (nat_add m n)) :=
  refl Nat (succ (nat_add m n))

def nat_add_succ_l (m n : Nat) : Eq Nat (nat_add (succ m) n) (succ (nat_add m n)) :=
  rec.Nat (fun n => Eq Nat (nat_add (succ m) n) (succ (nat_add m n)))
    (refl Nat (succ m))
    (fun n' : Nat => fun ih : Eq Nat (nat_add (succ m) n') (succ (nat_add m n')) =>
      eq_subst Nat (nat_add (succ m) n') (succ (nat_add m n'))
        (fun y => Eq Nat (succ (nat_add (succ m) n')) (succ y))
        ih
        (refl Nat (succ (nat_add (succ m) n'))))
    n

def nat_add_comm (m n : Nat) : Eq Nat (nat_add m n) (nat_add n m) :=
  rec.Nat (fun x => Eq Nat (nat_add x n) (nat_add n x))
    (eq_sym Nat (nat_add n zero) n (nat_add_zero_r n))
    (fun m' : Nat => fun ih : Eq Nat (nat_add m' n) (nat_add n m') =>
      eq_subst Nat (nat_add n m') (nat_add m' n)
        (fun y => Eq Nat (succ y) (nat_add n (succ m')))
        (eq_sym Nat (nat_add m' n) (nat_add n m') ih)
        (eq_sym Nat (nat_add n (succ m')) (succ (nat_add n m')) (nat_add_succ_r n m')))
    m


def count_append (x : Nat) (xs ys : List Nat)
  : Eq Nat (list_count Nat nat_eq x (list_append Nat xs ys))
           (nat_add (list_count Nat nat_eq x xs) (list_count Nat nat_eq x ys)) :=
  rec.List Nat (fun zs => Eq Nat (list_count Nat nat_eq x (list_append Nat zs ys))
                                 (nat_add (list_count Nat nat_eq x zs) (list_count Nat nat_eq x ys)))
    (refl Nat (list_count Nat nat_eq x ys))
    (fun h : Nat => fun t : List Nat => fun ih : Eq Nat (list_count Nat nat_eq x (list_append Nat t ys)) (nat_add (list_count Nat nat_eq x t) (list_count Nat nat_eq x ys)) =>
      let a := list_count Nat nat_eq x t in
      let b := list_count Nat nat_eq x ys in
      rec.Bool (fun b' : Bool => Eq Nat
        (match b' : Nat with | true => succ (list_count Nat nat_eq x (list_append Nat t ys)) | false => list_count Nat nat_eq x (list_append Nat t ys))
        (nat_add (match b' : Nat with | true => succ a | false => a) b))
        (eq_subst Nat (nat_add (succ a) b) (succ (nat_add a b))
          (fun y : Nat => Eq Nat (succ (list_count Nat nat_eq x (list_append Nat t ys))) (succ y))
          (eq_sym Nat (succ (nat_add a b)) (nat_add (succ a) b) (nat_add_succ_l a b))
          (eq_subst Nat (list_count Nat nat_eq x (list_append Nat t ys)) (nat_add a b)
            (fun y : Nat => Eq Nat (succ (list_count Nat nat_eq x (list_append Nat t ys))) (succ y))
            ih
            (refl Nat (succ (list_count Nat nat_eq x (list_append Nat t ys))))))
        ih
        (nat_eq x h))
    xs


def count_filter_partition (p : Nat -> Bool) (x : Nat) (xs : List Nat)
  : Eq Nat (list_count Nat nat_eq x xs)
           (nat_add (list_count Nat nat_eq x (list_filter Nat p xs))
                    (list_count Nat nat_eq x (list_filter Nat (fun y : Nat => not (p y)) xs))) :=
  rec.List Nat (fun zs => Eq Nat (list_count Nat nat_eq x zs)
                                 (nat_add (list_count Nat nat_eq x (list_filter Nat p zs))
                                          (list_count Nat nat_eq x (list_filter Nat (fun y : Nat => not (p y)) zs))))
    (eq_subst Nat zero (nat_add zero zero)
      (fun y : Nat => Eq Nat zero y)
      (eq_sym Nat (nat_add zero zero) zero (nat_add_zero_r zero))
      (refl Nat zero))
    (fun h : Nat => fun t : List Nat => fun ih : Eq Nat (list_count Nat nat_eq x t)
          (nat_add (list_count Nat nat_eq x (list_filter Nat p t))
                   (list_count Nat nat_eq x (list_filter Nat (fun y : Nat => not (p y)) t))) =>
      let a := list_count Nat nat_eq x (list_filter Nat p t) in
      let b := list_count Nat nat_eq x (list_filter Nat (fun y : Nat => not (p y)) t) in
      rec.Bool (fun b' : Bool => forall (h_eq : Eq Bool (p h) b'),
        Eq Nat (match nat_eq x h : Nat with | true => succ (nat_add a b) | false => nat_add a b)
               (nat_add (match b' : Nat with
                         | true => match nat_eq x h : Nat with | true => succ a | false => a
                         | false => match nat_eq x h : Nat with | true => succ b | false => b)
                        (nat_add a b)))
        (fun h_true : Eq Bool (p h) true =>
          rec.Bool (fun b2 : Bool => Eq Nat (match b2 : Nat with | true => succ (nat_add a b) | false => nat_add a b)
                                     (match b2 : Nat with | true => succ (nat_add a b) | false => nat_add a b))
            (refl Nat (succ (nat_add a b)))
            (refl Nat (nat_add a b))
            (nat_eq x h))
        (fun h_false : Eq Bool (p h) false =>
          rec.Bool (fun b2 : Bool => Eq Nat (match b2 : Nat with | true => succ (nat_add a b) | false => nat_add a b)
                                     (match b2 : Nat with | true => nat_add (succ b) (nat_add a b) | false => nat_add b (nat_add a b)))
            (eq_subst Nat (nat_add b (nat_add a b)) (nat_add (nat_add a b) b)
              (fun y : Nat => Eq Nat (nat_add a b) y)
              (nat_add_comm b (nat_add a b))
              (refl Nat (nat_add a b)))
            (eq_subst Nat (succ (nat_add a b)) (nat_add (succ b) (nat_add a b))
              (fun y : Nat => Eq Nat (succ (nat_add a b)) y)
              (eq_sym Nat (nat_add (succ b) (nat_add a b)) (succ (nat_add a b)) (nat_add_succ_l b (nat_add a b)))
              (refl Nat (succ (nat_add a b))))
            (nat_eq x h))
        (p h)
        (refl Bool (p h)))
    xs


def NatPerm_refl (xs : List Nat) : NatPerm xs xs :=
  fun x => refl Nat (list_count Nat nat_eq x xs)

def NatPerm_trans (xs ys zs : List Nat) (h1 : NatPerm xs ys) (h2 : NatPerm ys zs) : NatPerm xs zs :=
  fun x => eq_subst Nat (list_count Nat nat_eq x ys) (list_count Nat nat_eq x zs)
    (fun y => Eq Nat (list_count Nat nat_eq x xs) y)
    (h2 x)
    (h1 x)


def safe_quicksort_fuel (A : Type) (le : A -> A -> Bool) (fuel : Nat) (xs : List A) : List A :=
  rec.Nat (fun _ => List A -> List A)
    (fun xs => xs)
    (fun fuel' ih => fun xs =>
      rec.List A (fun _ => List A)
        (nil A)
        (fun head tail _ =>
          list_append A (ih (list_filter A (fun x : A => not (le head x)) tail))
            (cons A head (ih (list_filter A (fun x : A => le head x) tail))))
        xs)
    fuel
    xs

def safe_quicksort (A : Type) (le : A -> A -> Bool) (xs : List A) : List A :=
  safe_quicksort_fuel A le (list_length A xs) xs


def safe_quicksort_fuel_perm (fuel : Nat) (xs : List Nat) : NatPerm xs (safe_quicksort_fuel Nat nat_le fuel xs) :=
  rec.Nat (fun fuel' => forall (zs : List Nat), NatPerm zs (safe_quicksort_fuel Nat nat_le fuel' zs))
    (fun zs => NatPerm_refl zs)
    (fun fuel' ih => fun zs =>
      rec.List Nat (fun ws => NatPerm ws (safe_quicksort_fuel Nat nat_le (succ fuel') ws))
        (NatPerm_refl (nil Nat))
        (fun head tail _ =>
          let left := list_filter Nat (fun x : Nat => not (nat_le head x)) tail in
          let right := list_filter Nat (fun x : Nat => nat_le head x) tail in
          let left_sorted := safe_quicksort_fuel Nat nat_le fuel' left in
          let right_sorted := safe_quicksort_fuel Nat nat_le fuel' right in
          fun x : Nat =>
            let c_tail := list_count Nat nat_eq x tail in
            let c_left := list_count Nat nat_eq x left in
            let c_right := list_count Nat nat_eq x right in
            let c_head := match nat_eq x head : Nat with | true => succ zero | false => zero in
            let c_append := list_count Nat nat_eq x (list_append Nat left_sorted (cons Nat head right_sorted)) in
            let eq_ih_left := ih left x in
            let eq_ih_right := ih right x in
            let eq_append := count_append x left_sorted (cons Nat head right_sorted) in
            let eq_cons :=
              rec.Bool (fun b => Eq Nat (list_count Nat nat_eq x (cons Nat head right_sorted))
                                       (nat_add (match b : Nat with | true => succ zero | false => zero) (list_count Nat nat_eq x right_sorted)))
                (refl Nat (succ (list_count Nat nat_eq x right_sorted)))
                (refl Nat (list_count Nat nat_eq x right_sorted))
                (nat_eq x head) in
            let eq_partition := count_filter_partition (fun y : Nat => not (nat_le head y)) x tail in
            let eq_partition_comm := nat_add_comm c_left c_right in
            eq_subst Nat (nat_add c_left c_right) c_tail
              (fun y => Eq Nat (match nat_eq x head : Nat with | true => succ y | false => y)
                                (nat_add (list_count Nat nat_eq x left_sorted) (list_count Nat nat_eq x (cons Nat head right_sorted))))
              (eq_sym Nat c_tail (nat_add c_left c_right) eq_partition)
              (eq_subst Nat (nat_add (list_count Nat nat_eq x left_sorted) (list_count Nat nat_eq x (cons Nat head right_sorted))) (nat_add c_left (nat_add c_head c_right))
                (fun y => Eq Nat (match nat_eq x head : Nat with | true => succ (nat_add c_left c_right) | false => nat_add c_left c_right) y)
                (eq_subst Nat (nat_add (list_count Nat nat_eq x left_sorted) (list_count Nat nat_eq x (cons Nat head right_sorted)))
                  (nat_add c_left (nat_add c_head c_right))
                  (fun y => Eq Nat y (nat_add c_left (nat_add c_head c_right)))
                  (eq_subst Nat (list_count Nat nat_eq x (list_append Nat left_sorted (cons Nat head right_sorted)))
                    (nat_add (list_count Nat nat_eq x left_sorted) (list_count Nat nat_eq x (cons Nat head right_sorted)))
                    (fun y => Eq Nat y (nat_add c_left (nat_add c_head c_right)))
                    eq_append
                    (eq_subst Nat (list_count Nat nat_eq x left_sorted) c_left
                      (fun y => Eq Nat (nat_add y (list_count Nat nat_eq x (cons Nat head right_sorted))) (nat_add c_left (nat_add c_head c_right)))
                      eq_ih_left
                      (eq_subst Nat (list_count Nat nat_eq x (cons Nat head right_sorted)) (nat_add c_head (list_count Nat nat_eq x right_sorted))
                        (fun y => Eq Nat (nat_add c_left y) (nat_add c_left (nat_add c_head c_right)))
                        eq_cons
                        (eq_subst Nat (list_count Nat nat_eq x right_sorted) c_right
                          (fun y => Eq Nat (nat_add c_left (nat_add c_head y)) (nat_add c_left (nat_add c_head c_right)))
                          eq_ih_right
                          (refl Nat (nat_add c_left (nat_add c_head c_right)))))))
                  (refl Nat (nat_add c_left (nat_add c_head c_right))))
                (match nat_eq x head : Eq Nat (match nat_eq x head : Nat with | true => succ (nat_add c_left c_right) | false => nat_add c_left c_right) (nat_add c_left (match nat_eq x head : Nat with | true => succ c_right | false => c_right)) with
                 | true => eq_subst Nat (succ (nat_add c_left c_right)) (nat_add c_left (succ c_right))
                     (fun y => Eq Nat (succ (nat_add c_left c_right)) y)
                     (eq_sym Nat (nat_add c_left (succ c_right)) (succ (nat_add c_left c_right)) (nat_add_succ_r c_left c_right))
                     (refl Nat (succ (nat_add c_left c_right)))
                 | false => refl Nat (nat_add c_left c_right))))
          zs)
    fuel
    xs


theorem safe_quicksort_perm (xs : List Nat) : NatPerm xs (safe_quicksort Nat nat_le xs) :=
  safe_quicksort_fuel_perm (list_length Nat xs) xs


def safe_quicksort_eq_quicksort (xs : List Nat) : Eq (List Nat) (safe_quicksort Nat nat_le xs) (quicksort Nat nat_le xs) :=
  refl (List Nat) (quicksort Nat nat_le xs)

theorem safe_quicksort_sorted (xs : List Nat) : SortedNat (safe_quicksort Nat nat_le xs) :=
  eq_subst (List Nat) (quicksort Nat nat_le xs) (safe_quicksort Nat nat_le xs)
    (fun y : List Nat => SortedNat y)
    (eq_sym (List Nat) (safe_quicksort Nat nat_le xs) (quicksort Nat nat_le xs) (safe_quicksort_eq_quicksort xs))
    (quicksort_sorted xs)

theorem safe_quicksort_correct (xs : List Nat)
  : And (SortedNat (safe_quicksort Nat nat_le xs)) (NatPerm xs (safe_quicksort Nat nat_le xs)) :=
  conj (SortedNat (safe_quicksort Nat nat_le xs)) (NatPerm xs (safe_quicksort Nat nat_le xs))
    (safe_quicksort_sorted xs)
    (safe_quicksort_perm xs)


theorem quicksort_perm (xs : List Nat) : NatPerm xs (quicksort Nat nat_le xs) :=
  eq_subst (List Nat) (safe_quicksort Nat nat_le xs) (quicksort Nat nat_le xs)
    (fun y : List Nat => NatPerm xs y)
    (safe_quicksort_eq_quicksort xs)
    (safe_quicksort_perm xs)
