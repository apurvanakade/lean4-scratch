import Mathlib.Tactic

/-!
# Euclid's lemma from the definition of a prime

**Euclid's lemma** says that if a prime `p` divides a product `m * n`, then `p`
divides `m` or `p` divides `n`. We prove it starting from nothing but the
elementary school definition of a prime:

  `p` is prime iff `2 ≤ p` and the only divisors of `p` are `1` and `p`.

## Why the route is indirect

Euclid's lemma looks obvious, but it genuinely needs an argument: nothing in the
definition above mentions products at all. (It really can fail in other rings —
in `ℤ[√-5]` the element `2` has no proper divisors, yet `2 ∣ 6 = (1+√-5)(1-√-5)`
while dividing neither factor.) So we must actually use something special about
`ℕ`, and the classical route is via the Euclidean algorithm:

1. **Bézout's identity** (`exists_bezout`): `gcd m n = a * m + b * n` for some
   integers `a, b`. This is proved by the recursion that drives the Euclidean
   algorithm.
2. **A prime is coprime to what it does not divide**
   (`gcd_eq_one_of_prime_not_dvd`): if `p ∤ m` then `gcd p m = 1`, because
   `gcd p m` is a divisor of `p` and so is `1` or `p` — and it is not `p`.
3. **Gauss's lemma** (`dvd_of_gcd_eq_one`): coprimality plus Bézout gives that
   `k ∣ m * n` and `gcd k m = 1` force `k ∣ n`. Euclid's lemma follows at once.

Note that we may not use Mathlib's `Nat.Prime.dvd_or_dvd`, since that is exactly
the statement we are proving; the last section bridges back to it.

## Why integers appear in a statement about naturals

Bézout's coefficients must be allowed to be **negative** — e.g.
`gcd 3 5 = 1 = 2 * 3 + (-1) * 5`. So even though every quantity we care about is
a natural number, the identity itself only makes sense in `ℤ`, and the proofs
below move back and forth between `ℕ` and `ℤ`.

## Notes for readers new to Lean

* `m ∣ n` is divisibility, and it *unfolds to* `∃ c, n = m * c`. So a proof of
  `m ∣ n` is literally a pair (witness `c`, proof that `n = m * c`), written
  `⟨c, proof⟩`; and `obtain ⟨c, hc⟩ := hdvd` takes such a proof apart.
* `(n : ℤ)` is the natural number `n` viewed as an integer. These *coercions* are
  bookkeeping noise with no mathematical content, and the tactic `exact_mod_cast`
  discharges goals that are true "up to" moving between `ℕ` and `ℤ`.
* `ring` proves any identity valid in every commutative ring, and
  `linear_combination h` proves a goal that follows from `h` by rearranging.
* `⟨a, b, proof⟩` supplies the witnesses for a goal of the form `∃ a b, ...`.
* `Nat.gcd.induction` is induction along the Euclidean algorithm: to prove a
  statement for all `m n`, prove it when `m = 0`, and prove it for `m n` given
  that it holds for `n % m` and `m`.
* `rcases`/`obtain` do case analysis; `by_cases h : P` splits on whether `P`
  holds.
-/

/-- The elementary definition of primality: `p` is at least `2` and its only divisors
are `1` and `p`. -/
def IsPrimeNat (p : ℕ) : Prop :=
  2 ≤ p ∧ ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p

/-! ## Step 1: Bézout's identity -/

/-- The division algorithm, transported to `ℤ`: the remainder `n % m` equals
`n - (n / m) * m`. This is the one place where the natural-number operations `/`
and `%` are related to subtraction, which is why we must be in `ℤ`. -/
lemma int_mod_eq (m n : ℕ) : ((n % m : ℕ) : ℤ) = (n : ℤ) - (n / m : ℕ) * m := by
  -- In `ℕ` we have `m * (n / m) + n % m = n`; cast that to `ℤ` and rearrange.
  have h : (m : ℤ) * ((n / m : ℕ) : ℤ) + ((n % m : ℕ) : ℤ) = (n : ℤ) := by
    exact_mod_cast Nat.div_add_mod n m
  linear_combination h

/-- **Bézout's identity.** The greatest common divisor of `m` and `n` is an integer
linear combination of `m` and `n`.

The induction is the one that drives the Euclidean algorithm, `gcd m n = gcd (n % m) m`
for `0 < m`: having written `gcd (n % m) m` as a combination of `n % m` and `m`, we
substitute `n % m = n - (n / m) * m` and collect terms. -/
theorem exists_bezout (m n : ℕ) : ∃ a b : ℤ, (Nat.gcd m n : ℤ) = a * m + b * n := by
  induction m, n using Nat.gcd.induction with
  | H0 n =>
      -- `gcd 0 n = n`, which is `0 * 0 + 1 * n`.
      exact ⟨0, 1, by simp⟩
  | H1 m n hm ih =>
      -- `ih : gcd (n % m) m = a * (n % m) + b * m`, and `gcd m n = gcd (n % m) m`.
      obtain ⟨a, b, hab⟩ := ih
      refine ⟨b - a * (n / m : ℕ), a, ?_⟩
      rw [Nat.gcd_rec m n, hab, int_mod_eq m n]
      ring

/-! ## Step 2: a prime is coprime to everything it does not divide -/

/-- If `p` is prime and `p ∤ m`, then `gcd p m = 1`: indeed `gcd p m` divides `p`, so it
is `1` or `p`, and it cannot be `p` since `gcd p m` divides `m` while `p` does not. -/
lemma gcd_eq_one_of_prime_not_dvd {p m : ℕ} (hp : IsPrimeNat p) (h : ¬ p ∣ m) :
    Nat.gcd p m = 1 := by
  -- `gcd p m` divides `p`, so by primality it is `1` or `p`.
  rcases hp.2 (Nat.gcd p m) (Nat.gcd_dvd_left p m) with hg | hg
  · exact hg
  · -- If it were `p`, then `p = gcd p m` would divide `m`, contradicting `h`.
    exact absurd (hg ▸ Nat.gcd_dvd_right p m) h

/-! ## Step 3: Gauss's lemma and Euclid's lemma -/

/-- **Gauss's lemma.** If `gcd k m = 1` and `k ∣ m * n`, then `k ∣ n`.

The idea in one line: multiply the Bézout identity `1 = a * k + b * m` through by
`n`, giving `n = a * k * n + b * (m * n)`. Both summands are divisible by `k` —
the first visibly, the second because `k ∣ m * n`. -/
lemma dvd_of_gcd_eq_one {k m n : ℕ} (hk : Nat.gcd k m = 1) (hdvd : k ∣ m * n) : k ∣ n := by
  obtain ⟨a, b, hab⟩ := exists_bezout k m
  rw [hk] at hab
  -- `hab : (1 : ℤ) = a * k + b * m`
  obtain ⟨c, hc⟩ := hdvd
  -- `hc : m * n = k * c`, cast to `ℤ`.
  have hc' : (m : ℤ) * n = k * c := by exact_mod_cast hc
  -- Multiply Bézout by `n` and substitute `m * n = k * c`.
  have key : (n : ℤ) = k * (a * n + b * c) :=
    calc (n : ℤ) = (a * k + b * m) * n := by rw [← hab]; ring
      _ = a * k * n + b * ((m : ℤ) * n) := by ring
      _ = a * k * n + b * (k * c) := by rw [hc']
      _ = k * (a * n + b * c) := by ring
  -- So `k ∣ n` over `ℤ`, hence over `ℕ`.
  have : (k : ℤ) ∣ (n : ℤ) := ⟨a * n + b * c, key⟩
  exact_mod_cast this

/-- **Euclid's lemma**, for the elementary definition of primality. If `p` does not
divide `m`, then `p` is coprime to `m` by Step 2, so Gauss's lemma applies. -/
theorem IsPrimeNat.dvd_or_dvd {p m n : ℕ} (hp : IsPrimeNat p) (h : p ∣ m * n) :
    p ∣ m ∨ p ∣ n := by
  by_cases hm : p ∣ m
  · exact Or.inl hm
  · exact Or.inr (dvd_of_gcd_eq_one (gcd_eq_one_of_prime_not_dvd hp hm) h)

/-! ## Bridging back to `Nat.Prime`

Everything above used only `IsPrimeNat`. Mathlib's `Nat.Prime` satisfies that
definition, so our result applies to it.
-/

/-- Mathlib's `Nat.Prime` implies the elementary definition. -/
lemma IsPrimeNat.of_nat_prime {p : ℕ} (hp : Nat.Prime p) : IsPrimeNat p :=
  ⟨hp.two_le, fun _ hm => (Nat.Prime.eq_one_or_self_of_dvd hp _ hm)⟩

/-- **`Nat.Prime.dvd_or_dvd`**, proved from the elementary definition of a prime. -/
theorem prime_dvd_or_dvd {p m n : ℕ} (hp : Nat.Prime p) (h : p ∣ m * n) :
    p ∣ m ∨ p ∣ n :=
  (IsPrimeNat.of_nat_prime hp).dvd_or_dvd h
