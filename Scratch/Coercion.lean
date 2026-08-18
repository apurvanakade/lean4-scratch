import Mathlib.Tactic

theorem sqrt2' : ¬ (∃ m n : ℕ, m ≠ 0 ∧ 2 * m ^ 2 = n ^ 2) := by
  sorry

theorem sqrt2 : ¬ (∃ m n : ℤ, m ≠ 0 ∧ 2 * m ^ 2 = n ^ 2) := by
  rintro ⟨m, n, hm, hmn⟩
  apply sqrt2'
  refine ⟨m.natAbs, n.natAbs, Int.natAbs_ne_zero.mpr hm, ?_⟩
  have m1 := Int.natAbs_pow_two m
  have n1 := Int.natAbs_pow_two n
  rw [← m1, ← n1] at hmn
  exact_mod_cast hmn

example : ¬ (∃ q : ℚ, 2 = q * q) := by
  rintro ⟨q, key⟩
  have h := Rat.eq_iff_mul_eq_mul.mp key
  have triv1 : (2 : ℚ).den = 1 := by norm_num
  have triv2 : (2 : ℚ).num = 2 := by norm_num
  rw [triv1, triv2, Rat.mul_self_den, Rat.mul_self_num] at h
  push_cast at h
  apply sqrt2
  refine ⟨(q.den : ℤ), q.num, ?_, ?_⟩
  · exact_mod_cast q.den_nz
  · nlinarith [h]

example (q : ℚ) : q.den ≠ 0 :=
  q.den_nz

example (m : ℤ) : m ^ 2 = (m.natAbs : ℤ) ^ 2 :=
  (Int.natAbs_pow_two m).symm
