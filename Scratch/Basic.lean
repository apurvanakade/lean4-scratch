import Mathlib.Tactic

-- Lean 4 / mathlib4 uses classical logic (the law of excluded middle) by
-- default, so no extra imports or options are needed to use it.

set_option pp.showLetValues true

theorem dvd_sub_one {p a : ℕ} : (p ∣ a) → (p ∣ a + 1) → p ∣ 1 := by
  intros hpa hpa1
  have h := Nat.dvd_sub hpa1 hpa
  simp at h
  sorry

-- dvd_sub_one : (p ∣ a) → (p ∣ a + 1) → (p ∣ 1)
--
-- m ∣ n := ∃ k : ℕ, n = m * k
-- p.Prime :=  2 ≤ p ∧ (∀ (m : ℕ), m ∣ p → m = 1 ∨ m = p)
-- Nat.Prime.one_lt : p.Prime → 1 < p
--
-- n ! := Nat.factorial n
-- Nat.factorial_pos : ∀ (n : ℕ), 0 < n !
-- Nat.dvd_factorial : 0 < m → m ≤ n → m ∣ n !
--
-- Nat.minFac n := smallest non-trivial factor of n
-- Nat.minFac_prime : n ≠ 1 → (Nat.minFac n).Prime
-- Nat.minFac_pos : ∀ (n : ℕ), 0 < Nat.minFac n
-- Nat.minFac_dvd : ∀ (n : ℕ), Nat.minFac n ∣ n

theorem exists_infinite_primes (n : ℕ) : ∃ p, Nat.Prime p ∧ p ≥ n := by
  set p := Nat.minFac (Nat.factorial n + 1) with hp_def
  have h_fact_pos := Nat.factorial_pos n
  have pp : p.Prime := Nat.minFac_prime (by omega)
  refine ⟨p, ?_, pp⟩
  by_contra h
  push_neg at h
  have hp1 : p ∣ Nat.factorial n := Nat.dvd_factorial pp.pos h.le
  have hp2 : p ∣ Nat.factorial n + 1 := hp_def ▸ Nat.minFac_dvd _
  have hp3 : p ∣ 1 := (Nat.dvd_add_right hp1).mp hp2
  exact pp.not_dvd_one hp3
