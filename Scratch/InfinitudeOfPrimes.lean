import Mathlib.Tactic

theorem exists_infinite_primes (n : ℕ) : ∃ p, p ≥ n ∧ p.Prime := by
  set p := Nat.minFac (Nat.factorial n + 1) with hp_def
  have h_fact_pos := Nat.factorial_pos n
  have pp : p.Prime := Nat.minFac_prime (by omega)
  refine ⟨p, ?_, pp⟩
  by_contra h
  push Not at h
  have hp1 : p ∣ Nat.factorial n := Nat.dvd_factorial pp.pos h.le
  have hp2 : p ∣ Nat.factorial n + 1 := hp_def ▸ Nat.minFac_dvd _
  have hp3 : p ∣ 1 := (Nat.dvd_add_right hp1).mp hp2
  exact pp.not_dvd_one hp3
