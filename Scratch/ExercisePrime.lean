import Mathlib.Tactic

example (P : Prop) : ¬ ¬ ¬ P → ¬ P := by
  intro nnnp p
  apply nnnp
  intro np
  apply np
  apply p

example (p : ℕ) : p.Prime → p = 2 ∨ p % 2 = 1 := by
  exact fun a => a.eq_two_or_odd

#check @Nat.Prime.eq_two_or_odd

lemma eq_two_of_even_prime {p : ℕ} (hp : p.Prime) (h_even : Even p) : p = 2 := by
  rcases hp.eq_two_or_odd with h | h
  · exact h
  · rw [← Nat.not_even_iff] at h
    exact absurd h_even h

lemma even_of_odd_add_odd
    {a b : ℕ} (ha : ¬ Even a) (hb : ¬ Even b) :
    Even (a + b) := by
  rw [Nat.even_add]
  tauto

lemma one_lt_of_nontrivial_factor
    {b c : ℕ} (hb : b < b * c) :
    1 < c := by
  rcases c with _ | _ | c
  · simp at hb
  · simp at hb
  · omega

example (n : ℕ) : 0 < n ↔ n ≠ 0 := by
  omega

lemma nontrivial_product_of_not_prime
    {k : ℕ} (hk : ¬ k.Prime) (two_le_k : 2 ≤ k) :
    ∃ a b, a < k ∧ b < k ∧ 1 < a ∧ 1 < b ∧ a * b = k := by
  obtain ⟨a, ha_dvd, ha2, ha_lt⟩ := Nat.exists_dvd_of_not_prime2 two_le_k hk
  obtain ⟨b, hb⟩ := ha_dvd
  have hab : a < a * b := hb ▸ ha_lt
  have hb2 : 1 < b := one_lt_of_nontrivial_factor hab
  have hbk : b < k := by
    rw [hb]
    nlinarith
  exact ⟨a, b, ha_lt, hbk, ha2, hb2, hb.symm⟩

theorem three_fac_of_sum_consecutive_primes
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (p_ne_2 : p ≠ 2) (q_ne_2 : q ≠ 2)
    (consecutive : ∀ k, p < k → k < q → ¬ k.Prime) :
    ∃ a b c, p + q = a * b * c ∧ a > 1 ∧ b > 1 ∧ c > 1 := by
  refine ⟨2, ?_⟩
  have h1 : Even (p + q) := by
    apply even_of_odd_add_odd
    · contrapose! p_ne_2; exact eq_two_of_even_prime hp p_ne_2
    · contrapose! q_ne_2; exact eq_two_of_even_prime hq q_ne_2
  obtain ⟨k, hk⟩ := h1
  have hk' : ¬ k.Prime := consecutive k (by omega) (by omega)
  have h2k : 2 ≤ k := by have := hp.two_le; omega
  obtain ⟨b, c, hbk, hck, hb1, hc1, hbc⟩ := nontrivial_product_of_not_prime hk' h2k
  refine ⟨b, c, ?_, by norm_num, hb1, hc1⟩
  rw [hk, ← hbc]
  ring
