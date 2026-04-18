universe u
namespace C1

namespace Q1
  def compose {A B C: Type} (g: B -> C) (f: A -> B): A -> C :=
    fun x => g (f x)
  end Q1

namespace Q2
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

namespace Q3
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

namespace Q4
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

namespace Q5
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

-- 6
def prod (A B: Type): Type := (x: Bool) -> rec_bool A B x
def pair {A B: Type} (a: A) (b: B): prod A B :=
  ind_bool a b
--TODO product induction

-- 7

namespace Q8
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

  theorem add_ident: ∀ {n: Nat}, (n = add 0 n ∧ n = add n 0) := by
    intro n
    induction n with
    | zero => apply And.intro (by rfl) (by rfl)
    | succ m ih =>
        have h1: m = add m 0 := ih.right
        have h2: Nat.succ m = Nat.succ (add m 0) := by rw[<-h1]
        apply And.intro (by rfl) (h2)

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
    have add_zero_comm (n: Nat): (add 0 n = add n 0) := by
      have h1: n = add 0 n := add_ident.left
      have h2: n = add n 0 := add_ident.right
      apply Eq.trans (Eq.symm h1) h2
    have add_one_comm (n: Nat): (add 1 n = add n 1) := by
      induction n with
      | zero => exact add_zero_comm 1
      | succ m ih => calc
        add 1 (Nat.succ m) = add 1 (add 1 m) := by rfl
        _ = add 1 (add m 1) := by rw[ih]
        _ = add (add 1 m) 1 := add_assoc
        _ = add (Nat.succ m) 1 := by rfl
    intro m
    induction m with
    | zero => exact @add_zero_comm
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

end Q8

end C1
