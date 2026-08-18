import Mathlib.Tactic

-- a rw puzzle?
example
    (p : ℕ → Prop) (n : ℕ) (hn : p n)
    (h8 : ∀ n, p n ↔ p (n + 8))
    (h3 : ∀ n, p (n + 3) ↔ p n) :
    p (n + 1) := by
  rw [← h3] at hn
  rw [← h3] at hn
  rw [← h3] at hn
  rw [h8]
  exact hn

example : Fin 0 ≠ Fin 1 := by
  have : ∃ b : Fin 1, True := ⟨0, trivial⟩
  intro h
  rw [← h] at this
  obtain ⟨k, _⟩ := this
  exact k.elim0

-- when i started i thought this would be a rw puzzle, but it's not
theorem reflexive_of_symmetric_and_transitive (r : ℕ → ℕ → Prop)
    (h_symm : Std.Symm r) (h_trans : IsTrans ℕ r)
    (h_connected : ∀ x, ∃ y, r x y) :
    Std.Refl r where
  refl x := by
    obtain ⟨y, hy⟩ := h_connected x
    exact h_trans.trans x y x hy (h_symm.symm x y hy)

lemma even_or_odd (n : ℕ) :
    (∃ k, n = 2 * k) ∨ ∃ k, n = 2 * k + 1 := by
  induction n with
  | zero => left; exact ⟨0, by simp⟩
  | succ d hd =>
    obtain ⟨k, hk⟩ | ⟨k, hk⟩ := hd
    · right; exact ⟨k, by rw [hk]⟩
    · left; exact ⟨k + 1, by rw [hk]; ring⟩

-- I don't think I can do this without coercions
example
    (p : ℤ → Prop)
    (p_succ : ∀ n, p n → p (n + 1))
    (p_pred : ∀ n, p n → p (n - 1)) :
    (∀ n, p n) ↔ p 0 := by
  have key1 : ∀ n, p n ↔ p (n + 1) := by
    intro n
    constructor
    · intro h
      exact p_succ n h
    · intro h
      have := p_pred (n + 1) h
      simpa using this
  constructor
  · intro h
    exact h 0
  · intro h n
    match n with
    | Int.ofNat m =>
      induction m with
      | zero => simpa
      | succ d hd =>
        rw [show (Int.ofNat (d + 1) : ℤ) = (Int.ofNat d : ℤ) + 1 by simp]
        rw [← key1]
        exact hd
    | Int.negSucc m =>
      induction m with
      | zero => rw [key1]; simpa
      | succ d hd =>
        have heq : Int.negSucc (d + 1) + 1 = Int.negSucc d := by
          simp [Int.negSucc_eq]
        rw [key1, heq]
        exact hd

-- by landing in ℕ recursion (rather than subtraction), we avoid the perils
-- of nat subtraction
def f : ℕ → ℕ
  | 0 => 0
  | (n + 1) => n + 1 + f n

example : f 1 = 1 := by
  decide

example (n : ℕ) : 2 * f n = n * (n + 1) := by
  induction n with
  | zero => unfold f; simp
  | succ d hd =>
    unfold f
    ring_nf
    ring_nf at hd
    omega

variable {R : Type*} [CommRing R]

example (n : ℕ) (a : R) :
    (1 - a) * ∑ k ∈ Finset.range n, a ^ k = 1 - a ^ n := by
  rw [Finset.mul_sum]
  exact Finset.sum_range_induction (fun k => (1 - a) * a ^ k) (fun n => 1 - a ^ n)
    (by simp) n (fun k _ => by ring)

-- doing your induction "by hand"
example (n : ℕ) (a : R) :
    (1 - a) * ∑ k ∈ Finset.range n, a ^ k = 1 - a ^ n := by
  induction n with
  | zero => simp
  | succ d hd =>
    rw [Finset.sum_range_succ, mul_add, hd]
    ring
