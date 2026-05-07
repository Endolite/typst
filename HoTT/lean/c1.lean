section C1

section Q1
  def compose {A B C: Type} (g: B -> C) (f: A -> B): A -> C :=
    fun x => g (f x)
end Q1

section Q2
  def rec_prod {A B C: Type} (f: A -> B -> C): (A × B) -> C :=
    fun x => f x.1 x.2
  theorem rec_prod_def:
    ∀ {A B C: Type} {f: A -> B -> C} {a: A} {b: B},
    rec_prod f (a, b) = f a b :=
    by
      intros
      rfl

  def rec_sigma {A: Type} (B: A -> Type) {C: Type}
    (f: (x: A) -> (B x) -> C): (x: A) × (B x) -> C :=
    fun x => f x.1 x.2
  theorem rec_sigma_def:
    ∀ {A C: Type} {B: A -> Type} {f: (x: A) -> (B x) -> C} {a: A} {b: B a},
    rec_sigma B f ⟨a, b⟩ = f a b :=
    by
      intros
      rfl
end Q2

section Q3
  theorem uniq_prod:
    ∀ {A B: Type} {x: A × B}, (x.1, x.2) = x :=
    by
      intros
      rfl
  def ind_prod {A B: Type} (C: A × B -> Type) (f: (x: A) -> (y: B) -> C (x, y)):
    (p: A × B) -> C p :=
    fun x => f x.1 x.2
  theorem ind_prod_def:
    ∀ {A B: Type}
    {C: A × B -> Type}
    {f: (x: A) -> (y: B) -> C (x, y)}
    {a: A} {b: B},
    (ind_prod C f) (a, b) = f a b :=
    by
      intros
      apply_rules [uniq_prod]
end Q3

section Q4
  def iter {C: Type} (c0: C) (cs: C -> C): Nat -> C :=
    fun (n: Nat) =>
      match n with
      | 0 => c0
      | Nat.succ n => cs (iter c0 cs n)
  def rec_Nat {C: Type} (c0: C) (cs: Nat -> C -> C): Nat -> C :=
    fun (n: Nat) =>
      (iter (0, c0) (fun p: Nat × C => (Nat.succ p.1, cs p.1 p.2)) n).2
end Q4

def rec_bool {C: Type u} (a b: C): Bool -> C :=
  fun (x: Bool) =>
    if x then b else a
def ind_bool {C: Bool -> Type} (c0: C false) (c1: C true): (x: Bool) -> C x :=
  fun (x: Bool) =>
    match x with
    | false => c0
    | true => c1

section Q5
  def coprod (A B: Type): Type := (x: Bool) × (rec_bool A B x)
  def inl (A B: Type) (a: A): coprod A B := ⟨false, a⟩
  def inr (A B: Type) (b: B): coprod A B := ⟨true, b⟩
  def ind_coprod
    {A B: Type}
    (C: (coprod A B) -> Type)
    (g0: (x: A) -> C (inl A B x))
    (g1: (y: B) -> C (inr A B y)):
    (z: coprod A B) -> C z :=
      fun (z: coprod A B) =>
        Sigma.casesOn z (fun tag val =>
          match tag with
          | false => g0 val
          | true => g1 val
        )
  theorem ind_coprod_def:
    ∀
      {A B: Type}
      {C: (coprod A B) -> Type}
      {g0: (x: A) -> C (inl A B x)}
      {g1: (y: B) -> C (inr A B y)}
      {x: A}
      {y: B},
      ((ind_coprod C g0 g1) (inl A B x) = (g0 x))
        ∧ ((ind_coprod C g0 g1) (inr A B y) = (g1 y)) :=
        by
          intros
          constructor
          · simp [ind_coprod, inl]
          · simp [ind_coprod, inr]
end Q5

section Q6
  def prod (A B: Type): Type := (x: Bool) -> rec_bool A B x
  def pair {A B: Type} (a: A) (b: B): prod A B :=
  ind_bool a b
  --TODO product induction
end Q6

section Q7
  -- TODO
end Q7


section Q8
  def add (m n: Nat): Nat :=
    let c0 (n: Nat): Nat := n
    let cs (_: Nat) (g: Nat -> Nat) (n: Nat) := Nat.succ (g n)
    Nat.rec c0 cs m n
  def mul (m n: Nat): Nat :=
    let c0 (_: Nat): Nat := 0
    let cs (_: Nat) (g: Nat -> Nat) (n: Nat) := add n (g n)
    Nat.rec c0 cs n m
  def exp (m n: Nat): Nat :=
    let c0 (_: Nat): Nat := 1
    let cs (_: Nat) (g: Nat -> Nat) (n: Nat) := mul n (g n)
    Nat.rec c0 cs n m

  theorem add_ident: ∀ {n: Nat}, (add 0 n = n ∧ add n 0 = n) := by
    intro n
    induction n with
    | zero => apply And.intro (by rfl) (by rfl)
    | succ m ih =>
      have h1: m = add m 0 := Eq.symm ih.right
      have h2: Nat.succ m = Nat.succ (add m 0) := by rw[<-h1]
      apply And.intro (by rfl) (Eq.symm h2)

  theorem add_assoc: ∀ {i j k: Nat}, (add i (add j k) = add (add i j) k) := by
    intro i
    induction i with
    | zero =>
      intro j k
      have h1: add j k = add 0 (add j k) := add_ident.left
      have h2: add (add 0 j) k = add j k := add_ident.left
      apply Eq.trans h1 h2
    | succ m ih =>
      intro j k
      calc
        add (Nat.succ m) (add j k) = Nat.succ (add m (add j k)) := by rfl
        _ = Nat.succ (add (add m j) k) := by rw[ih]
        _ = add (add (Nat.succ m) j) k := by rfl

  theorem add_comm: ∀ {m n: Nat}, (add m n = add n m) := by
    have add_zero_comm: ∀ {n: Nat}, (add 0 n = add n 0) := by
      intro n
      have h1: n = add 0 n := add_ident.left
      have h2: n = add n 0 := by rw[add_ident.right]
      apply Eq.trans (Eq.symm h1) h2
    have add_one_comm: ∀ {n: Nat}, (add 1 n = add n 1) := by
      intro n
      induction n with
      | zero => exact add_zero_comm (n := 1)
      | succ m ih => calc
        add 1 (Nat.succ m) = add 1 (add 1 m) := by rfl
        _ = add 1 (add m 1) := by rw[ih]
        _ = add (add 1 m) 1 := add_assoc
        _ = add (Nat.succ m) 1 := by rfl
    intro m
    induction m with
    | zero => exact add_zero_comm
    | succ m ih =>
      intro n
      calc
        add (Nat.succ m) n = add (add 1 m) n := rfl
        _ = add 1 (add m n) := by rw[add_assoc]
        _ = add 1 (add n m) := by rw[ih]
        _ = add (add 1 n) m := by rw[add_assoc]
        _ = add (add n 1) m := by rw[add_one_comm]
        _ = add n (add 1 m) := by rw[add_assoc]
        _ = add n (Nat.succ m) := by rfl


    theorem mul_annihilator: ∀ {n: Nat}, (mul 0 n = 0 ∧ mul n 0 = 0) := by
      intro n
      induction n with
      | zero => apply And.intro (by rfl) (by rfl)
      | succ m ih => apply (And.intro
        (by calc
          mul 0 (Nat.succ m) = add 0 (mul 0 m) := by rfl
          _ = add 0 0 := by rw[ih.left]
          _ = 0 := by rfl
        )
        (by rfl)
      )

    theorem mul_ident: ∀ {n: Nat}, (mul 1 n = n ∧ mul n 1 = n) := by
      intro n
      induction n with
      | zero => apply And.intro (by rfl) (by rfl)
      | succ m ih => apply (And.intro
        (by calc
          mul 1 (Nat.succ m) = add 1 (mul 1 m) := by rfl
          _ = add 1 m := by rw[ih.left]
          _ = Nat.succ m := by rfl
        )
        (by calc
          mul (Nat.succ m) 1 = add (Nat.succ m) (mul (Nat.succ m) 0) := by rfl
          _ = add (Nat.succ m) 0 := by rw[mul_annihilator.right]
          _ = Nat.succ m := add_ident.right
        )
      )

    theorem mul_dist: ∀ {i j k: Nat},
    (mul i (add j k) = add (mul i j) (mul i k))
    ∧ (mul (add i j) k = add (mul i k) (mul j k)) :=
      have mul_dist_l: ∀ {j i k: Nat},
      (mul i (add j k) = add (mul i j) (mul i k)) := by
        intro j
        induction j with
        | zero =>
          intro i k
          apply Eq.symm (calc
            add (mul i 0) (mul i k) = add 0 (mul i k) := by rw[mul_annihilator.right]
            _ = mul i k := add_ident.left
            _ = mul i (add 0 k) := by rw[add_ident.left]
          )
        | succ j ih =>
          intro i k
          apply Eq.symm (calc
            add (mul i (Nat.succ j)) (mul i k) = add (mul i (add 1 j)) (mul i k) := by rfl
            _ = add (mul i (add j 1)) (mul i k) := by rw[add_comm (m := 1)]
            _ = add (add (mul i j) (mul i 1)) (mul i k) := by rw[<-ih]
            _ = add (add (mul i j) i) (mul i k) := by rw[mul_ident.right]
            _ = add (add i (mul i j)) (mul i k) := by rw[add_comm (n := i)]
            _ = add i (add (mul i j) (mul i k)) := by rw[add_assoc]
            _ = add i (mul i (add j k)) := by rw[<-ih]
            _ = mul i (Nat.succ (add j k)) := by rfl
            _ = mul i (add 1 (add j k)) := by rfl
            _ = mul i (add (add 1 j) k) := by rw[add_assoc]
            _ = mul i (add (Nat.succ j) k) := by rfl
          )
      have mul_dist_r: ∀ {k i j: Nat},
      (mul (add i j) k = add (mul i k) (mul j k)) := by
        intro k
        induction k with
        | zero =>
          intro i j
          apply Eq.symm (calc
            add (mul i 0) (mul j 0) = add 0 (mul j 0) := by rw[mul_annihilator.right]
            _ = add 0 0 := by rw[mul_annihilator.right]
            _ = 0 := by rfl
            _ = mul (add i j) 0 := by rw[mul_annihilator.right]
          )
        | succ k ih =>
          intro i j
          apply Eq.symm (calc
            add (mul i (Nat.succ k)) (mul j (Nat.succ k)) = add (add i (mul i k)) (add j (mul j k)) := by rfl
            _ = add (add i (mul i k)) (add (mul j k) j) := by rw[add_comm (m := j)]
            _ = add i (add (mul i k) (add (mul j k) j)) := by rw[add_assoc (i := i)]
            _ = add i (add (add (mul i k) (mul j k)) j) := by rw[add_assoc (i := (mul i k))]
            _ = add i (add (mul (add i j) k) j) := by rw[ih]
            _ = add i (add j (mul (add i j) k)) := by rw[add_comm (n := j)]
            _ = add (add i j) (mul (add i j) k) := by rw[add_assoc]
            _ = mul (add i j) (Nat.succ k) := by rfl
          )
        by apply And.intro mul_dist_l mul_dist_r

    theorem mul_comm: ∀ {m n: Nat}, (mul m n = mul n m) := by
      intro m
      induction m with
      | zero =>
        intro n
        calc
          mul 0 n = 0 := mul_annihilator.left
          _ = mul n 0 := by rw[mul_annihilator.right]
      | succ m ih =>
        intro n
        calc
          mul (Nat.succ m) n = mul (add 1 m) n := by rfl
          _ = (add (mul 1 n) (mul m n)) := mul_dist.right
          _ = (add n (mul m n)) := by rw[mul_ident.left]
          _ = (add n (mul n m)) := by rw[ih]
          _ = (add (mul n 1) (mul n m)) := by rw[mul_ident.right]
          _ = (add (mul n m) (mul n 1)) := by rw[add_comm]
          _ = mul n (add m 1) := by rw[mul_dist.left]
          _ = mul n (add 1 m) := by rw[add_comm]
          _ = mul n (Nat.succ m) := by rfl

    theorem mul_assoc: ∀ {i j k: Nat}, mul i (mul j k) = mul (mul i j) k := by
      intro i
      induction i with
      | zero =>
        intro j k
        apply Eq.symm (calc
          mul (mul 0 j) k = mul 0 k := by rw[mul_annihilator.left]
          _ = 0 := by exact mul_annihilator.left
          _ = mul 0 (mul j k) := by rw[mul_annihilator.left]
        )
      | succ i ih =>
        intro j k
        calc
          mul (Nat.succ i) (mul j k) = mul (add 1 i) (mul j k) := by rfl
          _ = add (mul 1 (mul j k)) (mul i (mul j k)) := mul_dist.right
          _ = add (mul j k) (mul i (mul j k)) := by rw[mul_ident.left]
          _ = add (mul j k) (mul (mul i j) k) := by rw[ih]
          _ = mul (add j (mul i j)) k := by rw[mul_dist.right]
          _ = mul (add j (mul j i)) k := by rw[mul_comm (m := i)]
          _ = mul (mul j (Nat.succ i)) k := by rfl
          _ = mul (mul (Nat.succ i) j) k := by rw[mul_comm (m := j)]

  structure Semiring where
    A: Type
    add: A -> A -> A
    zero: A
    mul: A -> A -> A
    one: A

    add_ident: ∀ {a: A}, (add zero a = a) ∧ (add a zero = a)
    add_comm: ∀ {a b: A}, add a b = add b a
    add_assoc: ∀ {a b c: A}, (add a (add b c)) = add (add a b) c

    mul_ident: ∀ {a: A}, (mul one a = a) ∧ (mul a one = a)
    mul_dist: ∀ {a b c: A},
      (mul a (add b c) = add (mul a b) (mul a c))
      ∧ (mul (add a b) c = add (mul a c) (mul b c))
    mul_assoc: ∀ {a b c: A}, mul a (mul b c) = mul (mul a b) c

  def nat_semiring: Semiring := {
      A := Nat,
      add := add,
      zero := 0,
      mul := mul,
      one := 1,

      add_ident := add_ident,
      add_comm := add_comm,
      add_assoc := add_assoc,

      mul_ident := mul_ident,
      mul_dist := mul_dist,
      mul_assoc := mul_assoc
    }
end Q8

section Q9
end Q9

end C1
