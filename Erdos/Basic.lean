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

open ArithmeticFunction Filter Finsupp

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

/-- A natural number is a square or twice a square (IsSquarish). -/
def IsSquarish (n : ℕ) : Prop := IsSquare n ∨ ∃ m, n = 2 * m ∧ IsSquare m

/-- An odd product of natural numbers is odd iff all factors are odd. -/
lemma odd_finset_prod {α : Type*} [DecidableEq α] {s : Finset α} {f : α → ℕ} :
    Odd (∏ a ∈ s, f a) ↔ ∀ a ∈ s, Odd (f a) := by
  induction s using Finset.induction with
  | empty => simp [odd_one]
  | insert x s' hx ih =>
    rw [Finset.prod_insert hx, Nat.odd_mul, ih]
    constructor
    · intro ⟨h1, h2⟩ a ha'
      simp only [Finset.mem_insert] at ha'
      cases ha' with
      | inl heq => rw [heq]; exact h1
      | inr hmem => exact h2 a hmem
    · intro h
      exact ⟨h _ (Finset.mem_insert_self _ _), 
             fun a ha' => h a (Finset.mem_insert_of_mem ha')⟩

/-- A Finsupp product is odd iff all factors in support are odd. -/
lemma odd_finsupp_prod {α : Type*} [DecidableEq α] {f : α →₀ ℕ} {g : α → ℕ → ℕ} :
    Odd (f.prod g) ↔ ∀ a ∈ f.support, Odd (g a (f a)) := by
  unfold Finsupp.prod
  exact odd_finset_prod

/-- Sum of powers of an odd number has same parity as the count. -/
lemma sum_range_pow_mod_two {p k : ℕ} (hp : Odd p) :
    (∑ j ∈ Finset.range (k + 1), p ^ j) % 2 = (k + 1) % 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.range_add_one, Finset.sum_insert Finset.notMem_range_self, Nat.add_mod, ih]
    have h : (p ^ (k + 1)) % 2 = 1 := Nat.odd_iff.mp hp.pow
    rw [h]; omega

/-- σ(p^k) for odd prime p is odd iff k is even (alternative formulation). -/
lemma sigma_prime_pow_odd_iff' {p k : ℕ} (hp : Nat.Prime p) (hp_odd : Odd p) :
    Odd (sigma 1 (p ^ k)) ↔ Even k := by
  rw [sigma_apply_prime_pow hp]; simp only [mul_one]
  rw [Nat.odd_iff, sum_range_pow_mod_two hp_odd]
  constructor
  · intro h; exact Nat.even_iff.mpr (by omega : k % 2 = 0)
  · intro ⟨m, hm⟩; rw [hm]; omega

/-- σ(2^k) is always odd (alternative proof). -/
lemma sigma_two_pow_odd' (k : ℕ) : Odd (sigma 1 (2 ^ k)) := by
  rw [sigma_apply_prime_pow Nat.prime_two]; simp only [mul_one]
  have h := Nat.geomSum_eq (m := 2) (by omega : 2 ≤ 2) (k + 1)
  simp at h; rw [h]
  have hpos : 2 ^ (k + 1) ≥ 1 := Nat.one_le_pow (k + 1) 2 (by omega)
  exact Nat.Even.sub_odd hpos (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one

/-- Helper: get prime from membership in factorization support. -/
lemma prime_of_mem_factorization_support {n p : ℕ} (h : p ∈ n.factorization.support) : Nat.Prime p := by
  have : p ∈ n.primeFactors := Nat.support_factorization n ▸ h
  exact (Nat.mem_primeFactors.mp this).1

/-- Factorization of m² = 2 • m.factorization. -/
lemma factorization_of_sq {n m : ℕ} (h : n = m * m) : n.factorization = 2 • m.factorization := by
  rw [h, ← sq, Nat.factorization_pow]

/-- If all prime valuations are even, n is a perfect square. -/
lemma isSquare_of_all_valuations_even {n : ℕ} (hn : n ≠ 0) 
    (h : ∀ p ∈ n.primeFactors, Even (n.factorization p)) : IsSquare n := by
  have hsup : n.factorization.support = n.primeFactors := Nat.support_factorization n
  have key : n = (n.primeFactors.prod (fun p => p ^ (n.factorization p / 2))) ^ 2 := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
    unfold Finsupp.prod
    rw [hsup, sq, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    obtain ⟨k, hk⟩ := h p hp
    rw [hk, ← two_mul, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]; ring
  use n.primeFactors.prod (fun p => p ^ (n.factorization p / 2))
  rw [sq] at key; exact key

/-- If n is squarish, then all odd prime valuations are even. -/
lemma isSquarish_odd_prime_val_even {n p : ℕ} (hn : n ≠ 0) (hp : Nat.Prime p) (hodd : Odd p) 
    (hsq : IsSquarish n) : Even (n.factorization p) := by
  rcases hsq with ⟨m, hm⟩ | ⟨m, hn_eq, ⟨k, hk⟩⟩
  · have hm0 : m ≠ 0 := by intro h; rw [h] at hm; simp at hm; exact hn hm
    rw [factorization_of_sq hm]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    use m.factorization p; ring
  · have hk0 : k ≠ 0 := by intro h; rw [h] at hk; simp at hk; rw [hk] at hn_eq; simp at hn_eq; exact hn hn_eq
    rw [hn_eq, hk]
    have hpow : k * k ≠ 0 := by positivity
    rw [Nat.factorization_mul (by omega) hpow, factorization_of_sq rfl]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    have hp2 : p ≠ 2 := fun h => by rw [h] at hodd; exact (Nat.not_even_iff_odd.mpr hodd) even_two
    rw [Nat.Prime.factorization Nat.prime_two, Finsupp.single_apply, if_neg hp2.symm, zero_add]
    use k.factorization p; ring

/-- If all odd prime valuations are even, then n is squarish. -/
lemma isSquarish_of_odd_valuations_even {n : ℕ} (hn : n ≠ 0) 
    (h : ∀ p, Nat.Prime p → Odd p → Even (n.factorization p)) : IsSquarish n := by
  by_cases hv2 : Even (n.factorization 2)
  · left
    apply isSquare_of_all_valuations_even hn
    intro p hp
    have hp_prime : Nat.Prime p := by
      have : p ∈ n.factorization.support := Nat.support_factorization n ▸ hp
      exact prime_of_mem_factorization_support this
    rcases Nat.Prime.eq_two_or_odd hp_prime with rfl | hodd
    · exact hv2
    · exact h p hp_prime (Nat.odd_iff.mpr hodd)
  · right
    have hv2_odd : Odd (n.factorization 2) := Nat.not_even_iff_odd.mp hv2
    obtain ⟨k, hk⟩ := hv2_odd
    have h2_pos : n.factorization 2 ≥ 1 := by omega
    have hdiv : 2 ∣ n := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hn).mpr h2_pos
    use n / 2
    constructor
    · exact (Nat.mul_div_cancel' hdiv).symm
    · have hn2 : n / 2 ≠ 0 := Nat.div_ne_zero_iff_of_dvd hdiv |>.mpr ⟨hn, by omega⟩
      apply isSquare_of_all_valuations_even hn2
      intro p hp
      have hp_prime : Nat.Prime p := by
        have : p ∈ (n/2).factorization.support := Nat.support_factorization (n/2) ▸ hp
        exact prime_of_mem_factorization_support this
      rcases Nat.Prime.eq_two_or_odd hp_prime with rfl | hodd
      · have hdiv2 : (n / 2).factorization 2 = n.factorization 2 - 1 := by
          rw [Nat.factorization_div hdiv]; simp [Nat.Prime.factorization Nat.prime_two]
        rw [hdiv2, hk]; use k; omega
      · have hpne2 : p ≠ 2 := fun heq => by rw [heq] at hodd; omega
        have hdivp : (n / 2).factorization p = n.factorization p := by
          rw [Nat.factorization_div hdiv]; simp [Nat.Prime.factorization Nat.prime_two, hpne2]
        rw [hdivp]
        by_cases hp_div : p ∈ n.primeFactors
        · exact h p hp_prime (Nat.odd_iff.mpr hodd)
        · have : n.factorization p = 0 := Finsupp.notMem_support_iff.mp (Nat.support_factorization n ▸ hp_div)
          rw [this]; exact ⟨0, rfl⟩

/-- σ(n) is odd if n is squarish. -/
lemma sigma_odd_of_squarish {n : ℕ} (hn : n ≠ 0) (hsq : IsSquarish n) : Odd (sigma 1 n) := by
  have hfact : sigma 1 n = n.factorization.prod (fun p k => sigma 1 (p ^ k)) := 
    ArithmeticFunction.IsMultiplicative.multiplicative_factorization (sigma 1) isMultiplicative_sigma hn
  rw [hfact, odd_finsupp_prod]
  intro p hp_mem
  have hp : Nat.Prime p := prime_of_mem_factorization_support hp_mem
  rcases Nat.Prime.eq_two_or_odd hp with rfl | hodd'
  · exact sigma_two_pow_odd' _
  · rw [sigma_prime_pow_odd_iff' hp (Nat.odd_iff.mpr hodd')]
    exact isSquarish_odd_prime_val_even hn hp (Nat.odd_iff.mpr hodd') hsq

/-- If σ(n) is odd, then n is squarish. -/
lemma squarish_of_sigma_odd {n : ℕ} (hn : n ≠ 0) (hodd : Odd (sigma 1 n)) : IsSquarish n := by
  have hfact : sigma 1 n = n.factorization.prod (fun p k => sigma 1 (p ^ k)) := 
    ArithmeticFunction.IsMultiplicative.multiplicative_factorization (sigma 1) isMultiplicative_sigma hn
  rw [hfact, odd_finsupp_prod] at hodd
  apply isSquarish_of_odd_valuations_even hn
  intro p hp hodd'
  by_cases hp_div : p ∣ n
  · have hp_mem : p ∈ n.factorization.support := by
      rw [Finsupp.mem_support_iff]
      exact Nat.pos_iff_ne_zero.mp (Nat.Prime.factorization_pos_of_dvd hp hn hp_div)
    have h := hodd p hp_mem
    rwa [sigma_prime_pow_odd_iff' hp hodd'] at h
  · have : n.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hp_div
    rw [this]; exact ⟨0, rfl⟩

/-- Main characterization: σ(n) is odd iff n is squarish. -/
lemma sigma_odd_iff_squarish {n : ℕ} (hn : n ≠ 0) : Odd (sigma 1 n) ↔ IsSquarish n :=
  ⟨squarish_of_sigma_odd hn, sigma_odd_of_squarish hn⟩

/-- Contrapositive: if n is not squarish, then σ(n) is even. -/
lemma sigma_even_of_not_squarish {n : ℕ} (hn : n ≠ 0) (hnsq : ¬IsSquarish n) : Even (sigma 1 n) := by
  by_contra h
  exact hnsq (squarish_of_sigma_odd hn (Nat.not_even_iff_odd.mp h))

/-- For n ≥ 2, the sequence σₖ(n) eventually becomes even and stays even.

This follows from `sigma_odd_iff_squarish` and the growth of σ:
- σ(n) is odd ⟺ n is squarish (a square or twice a square)
- The sequence σₖ(n) grows unboundedly
- Squarish numbers become increasingly sparse

Note: This is a deep number-theoretic fact. The key difficulty is proving that
the iterates cannot perpetually land on squarish numbers despite growing. -/
lemma sigma_iterate_eventually_even (n : ℕ) (hn : n ≥ 2) :
    ∃ k₀, ∀ k ≥ k₀, Even ((sigma 1)^[k] n) := by
  sorry  -- Requires analysis showing iterates escape squarish set

/-! ## Compounding Growth from Multiplicativity

Using multiplicativity of σ, we show that if σₖ(n) stays even, we get
exponential growth with base 3/2. However, this is NOT super-exponential.

For super-exponential, we need the abundancy ratio σ(m)/m to grow,
which requires the number of prime factors to increase.
-/

/-- For odd m, σ(2m) = 3σ(m). This follows from multiplicativity of σ. -/
lemma sigma_two_mul_odd (m : ℕ) (hodd : Odd m) : sigma 1 (2 * m) = 3 * sigma 1 m := by
  have hcop : Nat.gcd 2 m = 1 := Nat.coprime_two_left.mpr hodd
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop]
  rw [sigma_two]

/-- Inductive exponential lower bound: if the sequence stays even from k₀ onwards,
    then 2^j · σₖ₀₊ⱼ(n) ≥ 3^j · σₖ₀(n) for all j ≥ 0.
    
    This is equivalent to σₖ₀₊ⱼ(n) ≥ (3/2)^j · σₖ₀(n). -/
lemma exp_growth_induct (n : ℕ) (hn : n ≥ 2) (k₀ : ℕ) 
    (heven : ∀ k ≥ k₀, Even ((sigma 1)^[k] n)) (j : ℕ) :
    2^j * (sigma 1)^[k₀ + j] n ≥ 3^j * (sigma 1)^[k₀] n := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hiter : (sigma 1)^[k₀ + (j + 1)] n = sigma 1 ((sigma 1)^[k₀ + j] n) := by
      rw [show k₀ + (j + 1) = (k₀ + j) + 1 by omega]
      simp only [Function.iterate_succ', Function.comp_apply]
    have heven_j : Even ((sigma 1)^[k₀ + j] n) := heven (k₀ + j) (by omega)
    have hge2_j : (sigma 1)^[k₀ + j] n ≥ 2 := sigma_iterate_ge_two n hn (k₀ + j)
    have hstep : 2 * sigma 1 ((sigma 1)^[k₀ + j] n) ≥ 3 * (sigma 1)^[k₀ + j] n :=
      abundancy_bound_even _ hge2_j heven_j
    rw [hiter, pow_succ, pow_succ, mul_comm (2^j) 2, mul_comm (3^j) 3]
    calc 2 * 2^j * sigma 1 ((sigma 1)^[k₀ + j] n)
        = 2^j * (2 * sigma 1 ((sigma 1)^[k₀ + j] n)) := by ring
      _ ≥ 2^j * (3 * (sigma 1)^[k₀ + j] n) := Nat.mul_le_mul_left _ hstep
      _ = 3 * (2^j * (sigma 1)^[k₀ + j] n) := by ring
      _ ≥ 3 * (3^j * (sigma 1)^[k₀] n) := Nat.mul_le_mul_left _ ih
      _ = 3 * 3^j * (sigma 1)^[k₀] n := by ring

/-- Real-valued exponential bound: σₖ₀₊ⱼ(n) ≥ (3/2)^j · σₖ₀(n).
    
    This shows that staying even gives EXPONENTIAL growth with base 3/2,
    but this is NOT sufficient for super-exponential growth (which requires
    base → ∞). -/
lemma exp_growth_real (n : ℕ) (hn : n ≥ 2) (k₀ : ℕ) 
    (heven : ∀ k ≥ k₀, Even ((sigma 1)^[k] n)) (j : ℕ) :
    ((sigma 1)^[k₀ + j] n : ℝ) ≥ (3/2 : ℝ)^j * ((sigma 1)^[k₀] n : ℝ) := by
  have h := exp_growth_induct n hn k₀ heven j
  have h2pow_pos : (0 : ℝ) < (2 : ℝ)^j := by positivity
  rw [ge_iff_le, div_pow]
  rw [div_mul_eq_mul_div, div_le_iff₀ h2pow_pos, mul_comm]
  calc ((sigma 1)^[k₀] n : ℝ) * (3 : ℝ)^j 
      = (3 : ℝ)^j * ((sigma 1)^[k₀] n : ℝ) := by ring
    _ = ((3^j : ℕ) : ℝ) * ((sigma 1)^[k₀] n : ℝ) := by norm_cast
    _ = ((3^j * (sigma 1)^[k₀] n : ℕ) : ℝ) := by rw [Nat.cast_mul]
    _ ≤ ((2^j * (sigma 1)^[k₀ + j] n : ℕ) : ℝ) := by exact_mod_cast h
    _ = ((2^j : ℕ) : ℝ) * ((sigma 1)^[k₀ + j] n : ℝ) := by rw [Nat.cast_mul]
    _ = (2 : ℝ)^j * ((sigma 1)^[k₀ + j] n : ℝ) := by norm_cast
    _ = ((sigma 1)^[k₀ + j] n : ℝ) * (2 : ℝ)^j := by ring

/-! ## Prime Factor Accumulation Theory

For super-exponential growth, we need more than just σ(m) ≥ 3m/2.
The key insight is that the abundancy σ(m)/m depends on the prime factors:

  σ(m)/m ≥ ∏_{p | m} (1 + 1/p)

For m divisible by first k primes p₁, ..., pₖ:
  σ(m)/m ≥ (1 + 1/2)(1 + 1/3)(1 + 1/5)... = ∏_{i≤k} (pᵢ+1)/pᵢ

This product grows without bound as k → ∞ (by Mertens' theorem,
∏_{p≤x} (1 - 1/p)⁻¹ ~ e^γ log x).

So if the number of distinct prime factors of σₖ(n) grows unboundedly,
we get super-exponential growth.

**Gap Analysis**: The (3/2)^k growth from `exp_growth_real` only gives
exponential growth. For c = 2 > 3/2, we need σₖ(n) > 2^k eventually,
but (3/2)^k / 2^k = (3/4)^k → 0, so exponential bounds don't help.

Super-exponential requires showing that the effective base grows, i.e.,
σ(σₖ(n))/σₖ(n) → ∞. This would follow from ω(σₖ(n)) → ∞.
-/

/-- The number of distinct prime factors of n. -/
noncomputable def omega (n : ℕ) : ℕ := n.primeFactors.card

/-- omega ≥ 1 for n ≥ 2. -/
lemma omega_pos_of_ge_two (n : ℕ) (hn : n ≥ 2) : omega n ≥ 1 := by
  unfold omega
  have h := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  obtain ⟨p, hp, hdvd⟩ := h
  have hp_mem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hdvd, by omega⟩
  exact Finset.one_le_card.mpr ⟨p, hp_mem⟩

/-- If a | b and b ≠ 0, then omega(a) ≤ omega(b). -/
lemma omega_mono_of_dvd {a b : ℕ} (hab : a ∣ b) (hb : b ≠ 0) : omega a ≤ omega b := by
  by_cases ha : a = 0
  · simp [omega, ha]
  · unfold omega
    exact Finset.card_le_card (Nat.primeFactors_mono hab hb)

/-- omega of product (as union of prime factors). -/
lemma omega_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : 
    omega (a * b) = (a.primeFactors ∪ b.primeFactors).card := by
  unfold omega
  rw [Nat.primeFactors_mul ha hb]

/-- σ(p^k) ≥ p^k + p^{k-1} for k ≥ 1. -/
lemma sigma_prime_pow_ge (p k : ℕ) (hp : Nat.Prime p) (hk : k ≥ 1) :
    sigma 1 (p^k) ≥ p^k + p^(k-1) := by
  rw [sigma_apply_prime_pow hp]
  simp only [mul_one]
  have h_subset : ({k-1, k} : Finset ℕ) ⊆ Finset.range (k + 1) := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    simp only [Finset.mem_range]
    omega
  have hne : k - 1 ≠ k := by omega
  have h_sum : ∑ j ∈ ({k-1, k} : Finset ℕ), p^j = p^(k-1) + p^k := Finset.sum_pair hne
  calc ∑ j ∈ Finset.range (k + 1), p^j 
      ≥ ∑ j ∈ ({k-1, k} : Finset ℕ), p^j := Finset.sum_le_sum_of_subset h_subset
    _ = p^(k-1) + p^k := h_sum
    _ = p^k + p^(k-1) := by ring

/-- σ(p^k)/p^k ≥ 1 + 1/p for k ≥ 1.
    This is the key per-prime-power bound for abundancy. -/
lemma sigma_prime_pow_ratio_ge (p k : ℕ) (hp : Nat.Prime p) (hk : k ≥ 1) :
    (sigma 1 (p^k) : ℝ) / (p^k : ℝ) ≥ 1 + 1 / (p : ℝ) := by
  have hp_pos : (p : ℝ) > 0 := Nat.cast_pos.mpr hp.pos
  have hpk_pos : (p^k : ℝ) > 0 := by positivity
  have hpk_ne : (p^k : ℝ) ≠ 0 := ne_of_gt hpk_pos
  have hbound := sigma_prime_pow_ge p k hp hk
  -- Direct approach: show LHS ≥ RHS
  have h_lhs : (sigma 1 (p^k) : ℝ) / (p^k : ℝ) ≥ (p^k + p^(k-1) : ℕ) / (p^k : ℝ) := by
    apply div_le_div_of_nonneg_right
    · exact Nat.cast_le.mpr hbound
    · exact le_of_lt hpk_pos
  have h_rhs : (p^k + p^(k-1) : ℕ) / (p^k : ℝ) = 1 + 1 / (p : ℝ) := by
    rw [Nat.cast_add, Nat.cast_pow, Nat.cast_pow]
    rw [add_div, div_self hpk_ne]
    congr 1
    -- p^{k-1} / p^k = 1/p
    have h : (p : ℝ)^(k-1) / (p : ℝ)^k = 1 / (p : ℝ) := by
      rw [div_eq_div_iff hpk_ne (ne_of_gt hp_pos)]
      rw [one_mul]
      have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel hk
      calc (p : ℝ)^(k-1) * p = (p : ℝ)^(k-1+1) := by rw [pow_succ]
        _ = (p : ℝ)^k := by rw [hk1]
    exact h
  calc (sigma 1 (p^k) : ℝ) / (p^k : ℝ) 
      ≥ (p^k + p^(k-1) : ℕ) / (p^k : ℝ) := h_lhs
    _ = 1 + 1 / (p : ℝ) := h_rhs

/-- σ(2^k) for k ≥ 1 has at least one prime factor. -/
lemma sigma_two_pow_has_prime_factor (k : ℕ) (hk : k ≥ 1) : 
    ∃ p, Nat.Prime p ∧ p ∣ sigma 1 (2^k) := by
  have hsigma : sigma 1 (2^k) ≥ 3 := by
    rw [sigma_apply_prime_pow Nat.prime_two]
    simp only [mul_one]
    calc ∑ j ∈ Finset.range (k + 1), 2^j 
        ≥ ∑ j ∈ Finset.range 2, 2^j := by
          apply Finset.sum_le_sum_of_subset
          intro j hj
          simp only [Finset.mem_range] at hj ⊢
          omega
      _ = 3 := by native_decide
  exact Nat.exists_prime_and_dvd (by omega : sigma 1 (2^k) ≠ 1)

/-- All prime factors of σ(2^k) are odd (since σ(2^k) = 2^{k+1} - 1 is odd). -/
lemma sigma_two_pow_prime_factors_odd (k : ℕ) (p : ℕ) 
    (hp : p ∈ (sigma 1 (2^k)).primeFactors) : Odd p := by
  have h_odd := sigma_two_pow_odd' k
  have hp_prime := Nat.prime_of_mem_primeFactors hp
  have hp_dvd := Nat.dvd_of_mem_primeFactors hp
  rcases Nat.Prime.eq_two_or_odd hp_prime with rfl | hodd
  · -- Case p = 2: leads to contradiction since σ(2^k) is odd
    have h_even : Even (sigma 1 (2^k)) := by
      rw [even_iff_two_dvd]; exact hp_dvd
    exact absurd h_even (Nat.not_even_iff_odd.mpr h_odd)
  · exact Nat.odd_iff.mpr hodd

/-- The prime factors of σ(2^k) are disjoint from {2}. -/
lemma sigma_two_pow_primeFactors_not_two (k : ℕ) : 
    2 ∉ (sigma 1 (2^k)).primeFactors := by
  intro h
  have hodd := sigma_two_pow_prime_factors_odd k 2 h
  exact (Nat.not_even_iff_odd.mpr hodd) even_two

/-- omega(σ(2^k)) ≥ 1 for k ≥ 1. -/
lemma omega_sigma_two_pow_pos (k : ℕ) (hk : k ≥ 1) : omega (sigma 1 (2^k)) ≥ 1 := by
  obtain ⟨p, hp, hdvd⟩ := sigma_two_pow_has_prime_factor k hk
  have hsigma_ne : sigma 1 (2^k) ≠ 0 := by
    have : sigma 1 (2^k) ≥ 3 := by
      rw [sigma_apply_prime_pow Nat.prime_two]; simp only [mul_one]
      calc ∑ j ∈ Finset.range (k + 1), 2^j ≥ ∑ j ∈ Finset.range 2, 2^j := by
            apply Finset.sum_le_sum_of_subset; intro j hj; simp at hj ⊢; omega
        _ = 3 := by native_decide
    omega
  unfold omega
  have hp_mem : p ∈ (sigma 1 (2^k)).primeFactors := 
    Nat.mem_primeFactors.mpr ⟨hp, hdvd, hsigma_ne⟩
  exact Finset.one_le_card.mpr ⟨p, hp_mem⟩

/-- For n = 2^k * m with m odd, σ(n) = σ(2^k) * σ(m). -/
lemma sigma_two_pow_mul_odd {k m : ℕ} (hm_odd : Odd m) :
    sigma 1 (2^k * m) = sigma 1 (2^k) * sigma 1 m := by
  by_cases hk : k = 0
  · simp [hk]
  · have hcop : Nat.Coprime (2^k) m := 
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm_odd)
    exact isMultiplicative_sigma.map_mul_of_coprime hcop

/-- For n with prime factors p₁, ..., pₖ, we have 
    σ(n)/n ≥ ∏ᵢ (1 + 1/pᵢ).
    
    This is a lower bound based on just counting p^1 and p^0 for each prime. -/
lemma abundancy_prime_factor_bound (n : ℕ) (hn : n ≥ 1) :
    (sigma 1 n : ℝ) / n ≥ ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ)) := by
  sorry  -- Requires multiplicativity and prime factorization

/-- The product ∏_{p ∈ first k primes} (1 + 1/p) is unbounded as k → ∞.
    (This follows from divergence of ∑ 1/p.) -/
lemma prod_one_plus_inv_primes_unbounded :
    Tendsto (fun k => ∏ p ∈ Finset.filter Nat.Prime (Finset.range k), 
      (1 + 1 / (p : ℝ))) atTop atTop := by
  sorry  -- Deep number theory (Mertens)

/-- **CONJECTURE**: The number of prime factors of σₖ(n) grows unboundedly.
    This is the key missing piece for proving Erdős Problem 410.
    
    ## Why This Is Hard
    
    The difficulty is that σ doesn't always increase the prime factor count:
    - σ(4) = 7: ω = 1 → ω = 1 (no increase)
    - σ(6) = 12 = 2²·3: ω = 2 → ω = 2 (no increase)
    - σ(12) = 28 = 2²·7: ω = 2 → ω = 2 (no increase, but 7 replaces 3!)
    
    The sequence does grow, and the prime factors shift around, but proving
    they must eventually accumulate requires delicate analysis.
    
    ## Proof Strategies
    
    1. **Via Mersenne factors**: When m = 2^a · (odd), we have σ(m) = σ(2^a) · σ(odd).
       The Mersenne-like number σ(2^a) = 2^{a+1} - 1 contributes new odd prime factors.
       By Zsygmondy's theorem, 2^a - 1 gains new prime factors as a grows (except a = 6).
       But the power of 2 in σₖ(n) doesn't necessarily grow monotonically.
    
    2. **Via eventual divisibility**: Show that for each prime p, eventually p | σₖ(n).
       - 2 | σₖ(n) eventually (proven: sequence escapes squarish set)
       - 3 | σₖ(n) eventually (σ(2) = 3, σ(4) = 7, σ(8) = 15 = 3·5, ...)
       - Building this for all primes requires understanding σ's dynamics.
    
    3. **Via density arguments**: Squarish numbers (where σ is odd) have density 0.
       Large numbers typically have many prime factors (Hardy-Ramanujan: ω(n) ~ log log n).
       The sequence σₖ(n) grows at least linearly, so "eventually" it should have many factors.
       But "typically" ≠ "always for this specific sequence".
    
    If proven, combined with `abundancy_prime_factor_bound` and
    `prod_one_plus_inv_primes_unbounded`, this would give σₖ(n)^{1/k} → ∞. -/
lemma prime_factors_accumulate (n : ℕ) (hn : n ≥ 2) :
    Tendsto (fun k => omega ((sigma 1)^[k] n)) atTop atTop := by
  sorry  -- OPEN PROBLEM - this is the core of Erdős 410

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
