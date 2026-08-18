import Mathlib.Tactic

lemma two_dvd_of_two_dvd_sq {n : ℕ} (hn : 2 ∣ n ^ 2) : 2 ∣ n := by
  apply Nat.Prime.dvd_of_dvd_pow
  · exact Nat.prime_two
  · exact hn

lemma two_dvd_of_two_dvd_sq' {m n : ℕ} (hmn : 2 * m ^ 2 = n ^ 2) : 2 ∣ n := by
  apply two_dvd_of_two_dvd_sq
  exact ⟨m ^ 2, hmn.symm⟩

example (a b c : ℕ) (hc : 0 < c) (h : c * a = c * b) : a = b := by
  rwa [Nat.mul_right_inj (by omega : c ≠ 0)] at h

lemma two_dvd_of_two_dvd_sq'' {m n : ℕ} (hmn : 2 * m ^ 2 = n ^ 2) : 2 ∣ m := by
  apply two_dvd_of_two_dvd_sq
  obtain ⟨k, hk⟩ := two_dvd_of_two_dvd_sq' hmn
  refine ⟨k ^ 2, ?_⟩
  rw [hk] at hmn
  rw [← Nat.mul_right_inj (by norm_num : (2:ℕ) ≠ 0)]
  ring_nf
  ring_nf at hmn
  linarith [hmn]

lemma gcd_div_left (a b : ℕ) : (Nat.gcd a b) ∣ a :=
  Nat.gcd_dvd_left a b

lemma gcd_div_right (a b : ℕ) : (Nat.gcd a b) ∣ b :=
  Nat.gcd_dvd_right a b

lemma eq_zero_of_sq_eq_zero (m : ℕ) (hm : m ^ 2 = 0) : m = 0 := by
  simpa using hm

lemma sq_eq_zero_iff_eq_zero (m : ℕ) : m ^ 2 = 0 ↔ m = 0 := by
  constructor
  · apply eq_zero_of_sq_eq_zero
  · intro h; rw [h]; ring

lemma coprime_of_div_gcd
    (m n m' n' k : ℕ)
    (hk : k = Nat.gcd m n)
    (hmk : m = k * m')
    (hnk : n = k * n')
    (hm : 0 < m)
    (_hn : 0 < n) :
    Nat.Coprime m' n' := by
  have key := Nat.gcd_mul_left k m' n'
  rw [← hmk, ← hnk, ← hk] at key
  have hk_pos : 0 < k := by rw [hk]; exact Nat.gcd_pos_of_pos_left n hm
  unfold Nat.Coprime
  have heq : k * Nat.gcd m' n' = k * 1 := by rw [← key]; ring
  exact Nat.eq_of_mul_eq_mul_left hk_pos heq

lemma wlog_nonzero {m n : ℕ} (hm : m ≠ 0) (hmn : 2 * m ^ 2 = n ^ 2) : n ≠ 0 := by
  intro hn
  subst hn
  have hm2 : m ^ 2 = 0 := by nlinarith
  exact hm ((sq_eq_zero_iff_eq_zero m).mp hm2)

lemma gcd_ne_zero {m n : ℕ} (hm : m ≠ 0) (_hn : n ≠ 0) : Nat.gcd m n ≠ 0 := by
  have := Nat.gcd_pos_of_pos_left n (Nat.pos_of_ne_zero hm)
  omega

lemma ne_zero_of_mul_ne_zero {m k m' : ℕ}
    (hm : m ≠ 0)
    (hkm : m = k * m') :
    m' ≠ 0 := by
  contrapose! hm
  rw [hkm, hm]
  ring

lemma wlog_coprime_aux {m n k : ℕ}
    (hmn : 2 * (k * m) ^ 2 = (k * n) ^ 2)
    (hk : k ≠ 0) :
    2 * m ^ 2 = n ^ 2 := by
  have hk2 : k ^ 2 ≠ 0 := by positivity
  have heq : k ^ 2 * (2 * m ^ 2) = k ^ 2 * n ^ 2 := by ring_nf; ring_nf at hmn; linarith
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk2) heq

lemma wlog_coprime {m n : ℕ} (hm : m ≠ 0) (hmn : 2 * m ^ 2 = n ^ 2) :
    ∃ m' n', m' ≠ 0 ∧ 2 * m' ^ 2 = n' ^ 2 ∧ Nat.Coprime m' n' := by
  set k := m.gcd n with hk_def
  have hn : n ≠ 0 := wlog_nonzero hm hmn
  have hk : k ≠ 0 := gcd_ne_zero hm hn
  have hkm : k ∣ m := gcd_div_left m n
  have hkn : k ∣ n := gcd_div_right m n
  obtain ⟨m', hkm'⟩ := hkm
  obtain ⟨n', hkn'⟩ := hkn
  refine ⟨m', n', ?_, ?_, ?_⟩
  · exact ne_zero_of_mul_ne_zero hm hkm'
  · rw [hkm', hkn'] at hmn
    exact wlog_coprime_aux hmn hk
  · exact coprime_of_div_gcd m n m' n' k hk_def hkm' hkn'
      (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)

lemma not_coprime_of_common_factor {m n k : ℕ}
    (hk : 1 < k) (_hm : m ≠ 0) (_hn : n ≠ 0) (hmk : k ∣ m) (hnk : k ∣ n) :
    ¬ Nat.Coprime n m := by
  intro hcop
  have hdvd := Nat.dvd_gcd hnk hmk
  unfold Nat.Coprime at hcop
  rw [hcop] at hdvd
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

lemma sqrt2_irrational_aux {m n : ℕ} (hm : m ≠ 0) (hmn : 2 * m ^ 2 = n ^ 2) : False := by
  obtain ⟨m', n', hm', hmn', hcop⟩ := wlog_coprime hm hmn
  apply not_coprime_of_common_factor (k := 2) (by norm_num) hm' (wlog_nonzero hm' hmn')
    (two_dvd_of_two_dvd_sq'' hmn') (two_dvd_of_two_dvd_sq' hmn')
  exact hcop.symm

theorem sqrt2_irrational :
    ¬ ∃ p q : ℕ, p ≠ 0 ∧ 2 * p ^ 2 = q ^ 2 := by
  rintro ⟨p, q, hp, hpq⟩
  exact sqrt2_irrational_aux hp hpq
