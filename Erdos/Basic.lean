import Mathlib

/-!
# Erdős Problem 410

*Reference:* [erdosproblems.com/410](https://www.erdosproblems.com/410)

Let σ₁(n) = σ(n), the sum of divisors function, and σₖ(n) = σ(σₖ₋₁(n)).
Is it true that for all n ≥ 2, lim_{k → ∞} σₖ(n)^{1/k} = ∞?

## ⚠️ IMMUTABLE THEOREM STATEMENT
The statement of `erdos_410` below is the canonical problem definition.
It MUST NOT be modified under any circumstances. All proof work must
target this exact statement. If the statement appears unprovable as
written, escalate to the advisor — do not alter the theorem.
-/

open ArithmeticFunction Filter

namespace Erdos410

/-- For any n ≥ 1, σ(n) ≥ n since n is always a divisor of itself. -/
lemma sigma_one_ge (n : ℕ) (hn : n ≥ 1) : sigma 1 n ≥ n := by
  rw [sigma_one_apply, ge_iff_le]
  exact Finset.single_le_sum (fun d _ => Nat.zero_le d)
    (Nat.mem_divisors_self n (Nat.one_le_iff_ne_zero.mp hn))

/-- For any n ≥ 2, σ(n) ≥ n + 1 since both 1 and n are divisors of n and 1 ≠ n. -/
lemma sigma_one_ge_succ (n : ℕ) (hn : n ≥ 2) : sigma 1 n ≥ n + 1 := by
  rw [sigma_one_apply, ge_iff_le, add_comm]
  have h1n : 1 ≠ n := by omega
  have hn0 : n ≠ 0 := by omega
  have hsub : ({1, n} : Finset ℕ) ⊆ n.divisors := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    cases hd with
    | inl h => rw [h]; exact Nat.one_mem_divisors.mpr hn0
    | inr h => rw [h]; exact Nat.mem_divisors_self n hn0
  have hsum : ∑ d ∈ ({1, n} : Finset ℕ), (d : ℕ) = 1 + n := Finset.sum_pair h1n
  calc 1 + n = ∑ d ∈ ({1, n} : Finset ℕ), d := hsum.symm
    _ ≤ ∑ d ∈ n.divisors, d := Finset.sum_le_sum_of_subset hsub

/-- For any n ≥ 2, σ(n) > n (strict inequality). -/
lemma sigma_one_gt (n : ℕ) (hn : n ≥ 2) : sigma 1 n > n := by
  have h := sigma_one_ge_succ n hn
  omega

/-- For any n ≥ 2, σ(n) ≥ 2. This follows immediately from σ(n) > n ≥ 2. -/
lemma sigma_one_ge_two (n : ℕ) (hn : n ≥ 2) : sigma 1 n ≥ 2 := by
  have h := sigma_one_gt n hn
  omega

/-- For any n ≥ 2 and k ≥ 0, the k-th iterate of σ is at least 2.
This is proved by induction: the base case is n ≥ 2, and each application
of σ preserves the property since σ(m) > m for m ≥ 2. -/
lemma sigma_iterate_ge_two (n : ℕ) (hn : n ≥ 2) (k : ℕ) :
    (sigma 1)^[k] n ≥ 2 := by
  induction k with
  | zero => simp [hn]
  | succ k ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    exact sigma_one_ge_two ((sigma 1)^[k] n) ih

/-- For any n ≥ 2 and k ≥ 0, the k-th iterate of σ is at least n + k.
This provides a linear lower bound on the iterated sum-of-divisors. -/
lemma sigma_iterate_ge (n : ℕ) (hn : n ≥ 2) (k : ℕ) :
    (sigma 1)^[k] n ≥ n + k := by
  induction k with
  | zero =>
    -- σ^[0](n) = n ≥ n + 0
    simp
  | succ k ih =>
    -- σ^[k+1](n) = σ(σ^[k](n))
    simp only [Function.iterate_succ', Function.comp_apply]
    -- By IH: σ^[k](n) ≥ n + k ≥ 2
    have hge2 : (sigma 1)^[k] n ≥ 2 := sigma_iterate_ge_two n hn k
    -- By sigma_one_ge_succ: σ(σ^[k](n)) ≥ σ^[k](n) + 1
    have hstep : sigma 1 ((sigma 1)^[k] n) ≥ (sigma 1)^[k] n + 1 :=
      sigma_one_ge_succ ((sigma 1)^[k] n) hge2
    -- Combine: σ(σ^[k](n)) ≥ σ^[k](n) + 1 ≥ n + k + 1 = n + (k + 1)
    omega

/-- The k-th iterate of σ tends to infinity as k → ∞.
This follows from the linear lower bound σₖ(n) ≥ n + k. -/
lemma sigma_iterate_tendsto_atTop (n : ℕ) (hn : n ≥ 2) :
    Tendsto (fun k => ((sigma 1)^[k] n : ℝ)) atTop atTop := by
  -- We have σₖ(n) ≥ n + k by sigma_iterate_ge
  -- The function k ↦ (n + k : ℝ) tends to atTop
  -- By monotonicity (tendsto_atTop_mono), σₖ(n) also tends to atTop
  have h_lower : ∀ k : ℕ, (n + k : ℝ) ≤ ((sigma 1)^[k] n : ℝ) := fun k => by
    have hnat : (sigma 1)^[k] n ≥ n + k := sigma_iterate_ge n hn k
    exact_mod_cast hnat
  have h_tendsto_lower : Tendsto (fun k : ℕ => (n + k : ℝ)) atTop atTop := by
    have h1 : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    exact tendsto_atTop_add_const_left atTop (n : ℝ) h1
  exact tendsto_atTop_mono h_lower h_tendsto_lower

/-! ## Abundancy Lower Bound for Even Numbers

For even n ≥ 2, we have σ(n)/n ≥ 3/2. This is a key ingredient for showing
that iterated σ grows super-exponentially.
-/

/-- σ(2) = 3 (computed directly). -/
lemma sigma_two : sigma 1 2 = 3 := by
  rw [sigma_one_apply]
  have h : (2 : ℕ).divisors = {1, 2} := by decide
  rw [h]
  simp [Finset.sum_pair (by decide : (1:ℕ) ≠ 2)]

private lemma div_two_ne_one {n : ℕ} (hn : n ≥ 4) : n / 2 ≠ 1 := by omega

private lemma div_two_ne_self {n : ℕ} (hn : n ≥ 2) : n / 2 ≠ n := by omega

private lemma one_ne_self_of_ge_two {n : ℕ} (hn : n ≥ 2) : (1 : ℕ) ≠ n := by omega

/-- For even n ≥ 4, {1, n/2, n} is a subset of the divisors of n. -/
lemma subset_divisors_even (n : ℕ) (hn4 : n ≥ 4) (heven : Even n) :
    ({1, n / 2, n} : Finset ℕ) ⊆ n.divisors := by
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  have hn0 : n ≠ 0 := by omega
  cases hd with
  | inl h1 =>
    rw [h1]
    exact Nat.one_mem_divisors.mpr hn0
  | inr h2 =>
    cases h2 with
    | inl h_half =>
      rw [h_half, Nat.mem_divisors]
      exact ⟨Nat.div_dvd_of_dvd (Even.two_dvd heven), hn0⟩
    | inr h_n =>
      rw [h_n]
      exact Nat.mem_divisors_self n hn0

/-- The sum 1 + n/2 + n over the set {1, n/2, n} for n ≥ 4. -/
lemma sum_three_divisors (n : ℕ) (hn4 : n ≥ 4) :
    ∑ d ∈ ({1, n / 2, n} : Finset ℕ), d = 1 + n / 2 + n := by
  have h1 : (1 : ℕ) ≠ n / 2 := (div_two_ne_one hn4).symm
  have h2 : (1 : ℕ) ≠ n := one_ne_self_of_ge_two (by omega : n ≥ 2)
  have h3 : n / 2 ≠ n := div_two_ne_self (by omega : n ≥ 2)
  have h3' : n / 2 ∉ ({n} : Finset ℕ) := by simp [h3]
  have h12 : (1 : ℕ) ∉ ({n / 2, n} : Finset ℕ) := by simp [h1, h2]
  calc ∑ d ∈ ({1, n / 2, n} : Finset ℕ), d
      = ∑ d ∈ insert 1 {n / 2, n}, d := by rfl
    _ = 1 + ∑ d ∈ ({n / 2, n} : Finset ℕ), d := Finset.sum_insert h12
    _ = 1 + ∑ d ∈ insert (n / 2) {n}, d := by rfl
    _ = 1 + (n / 2 + ∑ d ∈ ({n} : Finset ℕ), d) := by rw [Finset.sum_insert h3']
    _ = 1 + (n / 2 + n) := by simp
    _ = 1 + n / 2 + n := by ring

/-- Lower bound for σ when n ≥ 4 is even: σ(n) ≥ 1 + n/2 + n. -/
lemma sigma_lower_bound_ge_four (n : ℕ) (hn4 : n ≥ 4) (heven : Even n) :
    sigma 1 n ≥ 1 + n / 2 + n := by
  rw [sigma_one_apply, ge_iff_le]
  calc 1 + n / 2 + n = ∑ d ∈ ({1, n / 2, n} : Finset ℕ), d := (sum_three_divisors n hn4).symm
    _ ≤ ∑ d ∈ n.divisors, d := Finset.sum_le_sum_of_subset (subset_divisors_even n hn4 heven)

/-- For even n ≥ 2, we have 2 * σ(n) ≥ 3 * n.
This is equivalent to σ(n)/n ≥ 3/2 (the abundancy lower bound). -/
lemma abundancy_bound_even (n : ℕ) (hn : n ≥ 2) (heven : Even n) :
    2 * sigma 1 n ≥ 3 * n := by
  rcases Nat.lt_or_eq_of_le hn with hn_gt | rfl
  · -- n > 2, and n is even so n ≥ 4
    have h4 : n ≥ 4 := by
      obtain ⟨k, hk⟩ := heven
      omega
    have hbound := sigma_lower_bound_ge_four n h4 heven
    -- σ(n) ≥ 1 + n/2 + n
    -- 2 * σ(n) ≥ 2 + n + 2n = 2 + 3n ≥ 3n
    calc 2 * sigma 1 n ≥ 2 * (1 + n / 2 + n) := by omega
      _ = 2 + 2 * (n / 2) + 2 * n := by ring
      _ = 2 + n + 2 * n := by rw [Nat.mul_div_cancel' (Even.two_dvd heven)]
      _ = 2 + 3 * n := by ring
      _ ≥ 3 * n := by omega
  · -- n = 2
    simp [sigma_two]

/-- For even n ≥ 2, the abundancy σ(n)/n is at least 3/2. -/
lemma abundancy_ratio_even (n : ℕ) (hn : n ≥ 2) (heven : Even n) :
    (sigma 1 n : ℝ) / n ≥ 3 / 2 := by
  have hn_pos : (0 : ℝ) < n := by positivity
  have hbound := abundancy_bound_even n hn heven
  rw [ge_iff_le, le_div_iff₀ hn_pos]
  -- Need: 3/2 * n ≤ σ(n)
  -- From hbound: 2 * σ(n) ≥ 3 * n
  -- So σ(n) ≥ 3*n/2 = 3/2 * n
  have h : (3 : ℝ) / 2 * n = 3 * n / 2 := by ring
  rw [h]
  have h2 : (3 * n : ℕ) ≤ 2 * sigma 1 n := hbound
  have h3 : (3 * n : ℝ) ≤ 2 * sigma 1 n := by exact_mod_cast h2
  linarith

/-! ## Sigma Parity Lemmas

The parity of σ(n) is determined by the prime factorization of n:
- σ(2^k) is always odd
- σ(p^k) for odd prime p is odd ⟺ k is even
- σ(n) is odd ⟺ n is a square or twice a square

These results are building blocks for showing that σₖ(n) is eventually even,
which in turn gives exponential growth with base ≥ 3/2.
-/

/-- The geometric sum ∑_{i=0}^{n-1} 2^i = 2^n - 1. -/
lemma sum_pow_two' (n : ℕ) : ∑ k ∈ Finset.range n, 2^k = 2^n - 1 := by
  have h := Nat.geomSum_eq (by norm_num : (2 : ℕ) ≤ 2) n
  have h2 : (2 : ℕ) - 1 = 1 := by norm_num
  rw [h2, Nat.div_one] at h
  exact h

/-- Helper: convert ¬Odd to Even for naturals. -/
lemma not_odd_to_even (n : ℕ) (h : ¬Odd n) : Even n := by
  rcases Nat.even_or_odd n with he | ho
  · exact he
  · exact (h ho).elim

/-- A sum of odd numbers is odd iff there are an odd number of them. -/
lemma odd_sum_odd_iff {ι : Type*} (s : Finset ι) (f : ι → ℕ) (hodd : ∀ i ∈ s, Odd (f i)) :
    Odd (∑ i ∈ s, f i) ↔ Odd s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.card_empty]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    simp only [Finset.card_insert_eq_ite, if_neg ha]
    have hodd_a : Odd (f a) := hodd a (Finset.mem_insert_self a s)
    have hodd_rest : ∀ i ∈ s, Odd (f i) := fun i hi => hodd i (Finset.mem_insert_of_mem hi)
    have ih' := ih hodd_rest
    rw [Nat.odd_add_one]
    constructor
    · intro h_total_odd h_card_odd
      have h_sum_odd : Odd (∑ x ∈ s, f x) := ih'.mpr h_card_odd
      have := Odd.add_odd hodd_a h_sum_odd
      rw [Nat.even_iff] at this
      rw [Nat.odd_iff] at h_total_odd
      omega
    · intro h_card_not_odd
      have h_sum_not_odd : ¬Odd (∑ x ∈ s, f x) := fun h => h_card_not_odd (ih'.mp h)
      rw [Nat.odd_iff, Nat.add_mod]
      have hodd_a' : f a % 2 = 1 := Nat.odd_iff.mp hodd_a
      have h_sum_even : (∑ x ∈ s, f x) % 2 = 0 := Nat.even_iff.mp (not_odd_to_even _ h_sum_not_odd)
      simp [hodd_a', h_sum_even]

/-- Helper: Odd (n+1) ↔ Even n. -/
lemma odd_succ_iff_even (n : ℕ) : Odd (n + 1) ↔ Even n := by
  constructor
  · intro h
    rw [Nat.odd_iff] at h
    rw [Nat.even_iff]
    omega
  · intro h
    rw [Nat.even_iff] at h
    rw [Nat.odd_iff]
    omega

/-- σ(2^k) = 2^(k+1) - 1, the Mersenne number. -/
lemma sigma_pow_two' (k : ℕ) : sigma 1 (2^k) = 2^(k+1) - 1 := by
  rw [sigma_apply_prime_pow (Nat.prime_two)]
  have h : ∀ j, 2^(j * 1) = 2^j := fun j => by ring_nf
  simp_rw [h]
  exact sum_pow_two' (k + 1)

/-- 2^(k+1) - 1 is always odd. -/
lemma pow_two_sub_one_odd (k : ℕ) : Odd (2^(k+1) - 1) := by
  rw [Nat.odd_iff]
  have h : 2^(k+1) ≥ 1 := Nat.one_le_pow (k+1) 2 (by norm_num)
  omega

/-- σ(2^k) is always odd. -/
lemma sigma_pow_two_odd (k : ℕ) : Odd (sigma 1 (2^k)) := by
  rw [sigma_pow_two']
  exact pow_two_sub_one_odd k

/-- For odd prime p, σ(p^k) is odd iff k is even. -/
lemma sigma_odd_prime_pow_iff (p k : ℕ) (hp : p.Prime) (hodd : Odd p) :
    Odd (sigma 1 (p^k)) ↔ Even k := by
  rw [sigma_apply_prime_pow hp]
  have h_eq : ∑ j ∈ Finset.range (k + 1), p ^ (j * 1) = ∑ j ∈ Finset.range (k + 1), p ^ j := by
    congr 1; ext j; ring_nf
  rw [h_eq]
  have hall_odd : ∀ j ∈ Finset.range (k+1), Odd (p^j) := fun j _ => hodd.pow
  rw [odd_sum_odd_iff (Finset.range (k+1)) (fun j => p^j) hall_odd]
  rw [Finset.card_range]
  exact odd_succ_iff_even k

/-- A natural number is a square or twice a square. -/
def isSquareOrTwiceSquare (n : ℕ) : Prop :=
  IsSquare n ∨ (∃ m, IsSquare m ∧ n = 2 * m)

/-- σ(n) is odd iff n is a square or twice a square.

This is a well-known number-theoretic result. The proof uses multiplicativity of σ
and the characterization of σ(p^k) parity:
- σ(2^a) is always odd
- σ(p^a) for odd p is odd ⟺ a is even
- n is a square or twice a square ⟺ all odd prime exponents in n are even -/
lemma sigma_odd_iff (n : ℕ) (hn : n ≠ 0) :
    Odd (sigma 1 n) ↔ isSquareOrTwiceSquare n := by
  sorry  -- Requires multiplicativity argument with prime factorization

/-- For n ≥ 2, the sequence σₖ(n) eventually becomes even and stays even.

This follows from `sigma_odd_iff` and the growth of σ:
- σ(n) is odd ⟺ n is a square or twice a square
- The sequence σₖ(n) grows unboundedly
- Squares and twice-squares become increasingly sparse -/
lemma sigma_iterate_eventually_even (n : ℕ) (hn : n ≥ 2) :
    ∃ k₀, ∀ k ≥ k₀, Even ((sigma 1)^[k] n) := by
  sorry  -- Requires sigma_odd_iff and analysis of iteration

/-! ## Super-Exponential Lower Bound (Partial Progress)

The main theorem `erdos_410` requires showing that σₖ(n)^{1/k} → ∞,
which is equivalent to: for any c > 0, eventually c^k < σₖ(n).

We split this into two cases:
- Case c ≤ 1: Trivial since σₖ(n) ≥ 2 for all k.
- Case c > 1: This is the CORE DIFFICULTY — requires showing super-exponential growth.

The case c > 1 is an **open problem in number theory**. It would follow from any of:
1. Showing that the abundancy σ(σₖ(n))/σₖ(n) tends to infinity
2. Showing that σₖ(n) accumulates arbitrarily many small prime factors
3. Showing that σₖ(n) eventually avoids being a perfect square often enough

See `problem.md` for references to Erdős-Granville-Pomerance-Spiro (1990) and
Guy's *Unsolved Problems in Number Theory* (2004), Problem B9.
-/

/-- For c ∈ (0, 1], eventually c^k < σₖ(n) (trivial case).
This follows immediately from σₖ(n) ≥ 2 and c^k ≤ 1 for c ≤ 1. -/
lemma sigma_iterate_superexp_le_one (n : ℕ) (hn : n ≥ 2) (c : ℝ) (hc_pos : c > 0) (hc_le : c ≤ 1) :
    ∃ k₀, ∀ k ≥ k₀, c ^ k < ((sigma 1)^[k] n : ℝ) := by
  use 0
  intro k _
  have h1 : c ^ k ≤ 1 := pow_le_one₀ (le_of_lt hc_pos) hc_le
  have h2 : (sigma 1)^[k] n ≥ 2 := sigma_iterate_ge_two n hn k
  calc c ^ k ≤ 1 := h1
    _ < 2 := by norm_num
    _ ≤ ((sigma 1)^[k] n : ℝ) := by exact_mod_cast h2

/-- **OPEN PROBLEM**: For c > 1, eventually c^k < σₖ(n).
This is the core difficulty in Erdős Problem #410.

To complete this lemma, we would need to prove one of:
- `abundancy_iterate_unbounded`: σ(σₖ(n))/σₖ(n) → ∞ as k → ∞
- `prime_factors_accumulate`: σₖ(n) divisible by first m primes for arbitrarily large m
- An explicit super-exponential lower bound on σₖ(n)

See the paper "On the normal behavior of the iterates of some arithmetical functions"
by Erdős, Granville, Pomerance, and Spiro (1990). -/
lemma sigma_iterate_superexp_gt_one (n : ℕ) (hn : n ≥ 2) (c : ℝ) (hc : c > 1) :
    ∃ k₀, ∀ k ≥ k₀, c ^ k < ((sigma 1)^[k] n : ℝ) := by
  sorry

/-- Combined super-exponential bound for any c > 0.
Proven for c ≤ 1; the case c > 1 requires `sigma_iterate_superexp_gt_one`. -/
lemma sigma_iterate_superexp (n : ℕ) (hn : n ≥ 2) (c : ℝ) (hc : c > 0) :
    ∃ k₀, ∀ k ≥ k₀, c ^ k < ((sigma 1)^[k] n : ℝ) := by
  rcases le_or_gt c 1 with hle | hgt
  · exact sigma_iterate_superexp_le_one n hn c hc hle
  · exact sigma_iterate_superexp_gt_one n hn c hgt

/-- Erdős Problem 410: Iterated sum-of-divisors grows super-exponentially.

DO NOT MODIFY THIS STATEMENT. This is the canonical formalization from
google-deepmind/formal-conjectures. -/
theorem erdos_410 : ∀ n > 1,
    Tendsto (fun k : ℕ ↦ ((sigma 1)^[k] n : ℝ) ^ (1 / (k : ℝ))) atTop atTop := by
  sorry

end Erdos410
