import Mathlib
import Archive.Wiedijk100Theorems.SumOfPrimeReciprocalsDiverges

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

/-- If p is in n's prime factors, then the factorization exponent is at least 1. -/
lemma factorization_pos_of_mem_primeFactors {n p : ℕ} (h : p ∈ n.primeFactors) :
    n.factorization p ≥ 1 := by
  rw [Nat.mem_primeFactors] at h
  have hne : n ≠ 0 := h.2.2
  have hdvd : p ∣ n := h.2.1
  exact Nat.Prime.factorization_pos_of_dvd h.1 hne hdvd

/-- For n with prime factors p₁, ..., pₖ, we have 
    σ(n)/n ≥ ∏ᵢ (1 + 1/pᵢ).
    
    This is a lower bound based on just counting p^1 and p^0 for each prime. -/
lemma abundancy_prime_factor_bound (n : ℕ) (hn : n ≥ 1) :
    (sigma 1 n : ℝ) / n ≥ ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ)) := by
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  -- Use multiplicativity: σ(n) = ∏_{p | n} σ(p^{fact p})
  have h_sigma : sigma 1 n = n.factorization.prod (fun p k => sigma 1 (p^k)) :=
    IsMultiplicative.multiplicative_factorization (sigma 1) isMultiplicative_sigma hn0
  -- n = ∏_{p | n} p^{fact p}
  have h_n : (n : ℕ) = n.factorization.prod (fun p k => p^k) :=
    (Nat.factorization_prod_pow_eq_self hn0).symm
  have hsup : n.factorization.support = n.primeFactors := Nat.support_factorization n
  -- Each factor p^k contributes positive real
  have h_all_pos : ∀ p ∈ n.primeFactors, (0 : ℝ) < (p : ℝ)^(n.factorization p) := fun p hp => by
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have hcasted : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp_prime.pos
    exact pow_pos hcasted (n.factorization p)
  -- Rewrite n as the product of prime powers (casted to ℝ)
  have h_n_cast : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ)^(n.factorization p) := by
    conv_lhs => rw [h_n]
    unfold Finsupp.prod
    rw [hsup]
    simp only [Nat.cast_prod, Nat.cast_pow]
  -- Rewrite σ(n) as product of σ(p^k) (casted to ℝ)
  have h_sigma_cast : (sigma 1 n : ℝ) = 
      ∏ p ∈ n.primeFactors, (sigma 1 (p^(n.factorization p)) : ℝ) := by
    conv_lhs => rw [h_sigma]
    unfold Finsupp.prod
    rw [hsup]
    simp only [Nat.cast_prod]
  -- Rewrite goal as product of ratios
  rw [h_sigma_cast, h_n_cast, ← Finset.prod_div_distrib]
  -- Apply pointwise bound: σ(p^k)/p^k ≥ 1 + 1/p
  apply Finset.prod_le_prod
  · intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp_prime.pos
    have h1 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    linarith
  · intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have hk := factorization_pos_of_mem_primeFactors hp
    exact sigma_prime_pow_ratio_ge p (n.factorization p) hp_prime hk

/-- Key helper: ∏(1 + f(x)) ≥ 1 + ∑f(x) for nonneg f. -/
lemma prod_one_add_ge_one_add_sum {ι : Type*} {s : Finset ι} {f : ι → ℝ}
    (hf : ∀ x ∈ s, 0 ≤ f x) : ∏ x ∈ s, (1 + f x) ≥ 1 + ∑ x ∈ s, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s' hx ih =>
    have hfx : 0 ≤ f x := hf x (Finset.mem_insert_self x s')
    have hfs' : ∀ y ∈ s', 0 ≤ f y := fun y hy => hf y (Finset.mem_insert_of_mem hy)
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    have hsum_nonneg : 0 ≤ ∑ y ∈ s', f y := Finset.sum_nonneg hfs'
    have hih : ∏ y ∈ s', (1 + f y) ≥ 1 + ∑ y ∈ s', f y := ih hfs'
    have h1fx_pos : 0 ≤ 1 + f x := by linarith
    have hprod_pos : 0 ≤ ∏ y ∈ s', (1 + f y) := by
      apply Finset.prod_nonneg
      intro y hy
      have := hfs' y hy
      linarith
    have h1sum_pos : 0 ≤ 1 + ∑ y ∈ s', f y := by linarith
    have step1 : (1 + f x) * ∏ y ∈ s', (1 + f y) ≥ (1 + f x) * (1 + ∑ y ∈ s', f y) := by
      apply mul_le_mul_of_nonneg_left hih h1fx_pos
    have step2 : (1 + f x) * (1 + ∑ y ∈ s', f y) =
        1 + f x + ∑ y ∈ s', f y + f x * ∑ y ∈ s', f y := by ring
    have h_cross_pos : 0 ≤ f x * ∑ y ∈ s', f y := mul_nonneg hfx hsum_nonneg
    linarith

/-- The product ∏_{p ∈ first k primes} (1 + 1/p) is unbounded as k → ∞.
    This follows from the divergence of ∑ 1/p (Euler's theorem, 1737).

    Proof strategy:
    - ∏ (1 + 1/p) ≥ 1 + ∑ 1/p by `prod_one_add_ge_one_add_sum`
    - ∑ 1/p → ∞ by `Theorems100.Real.tendsto_sum_one_div_prime_atTop`
    - Therefore ∏ (1 + 1/p) → ∞ -/
lemma prod_one_plus_inv_primes_unbounded :
    Tendsto (fun k => ∏ p ∈ Finset.filter Nat.Prime (Finset.range k),
      (1 + 1 / (p : ℝ))) atTop atTop := by
  -- The product ≥ 1 + sum of 1/p
  have h_lower_bound : ∀ k,
      1 + ∑ p ∈ Finset.filter Nat.Prime (Finset.range k), 1 / (p : ℝ) ≤
      ∏ p ∈ Finset.filter Nat.Prime (Finset.range k), (1 + 1 / (p : ℝ)) := fun k => by
    apply prod_one_add_ge_one_add_sum
    intro p _
    simp only [one_div, inv_nonneg]
    exact Nat.cast_nonneg p
  -- The sum diverges (from Erdős's proof in the Archive)
  have h_sum_unbounded :
      Tendsto (fun k => ∑ p ∈ Finset.filter Nat.Prime (Finset.range k), 1 / (p : ℝ))
        atTop atTop :=
    Theorems100.Real.tendsto_sum_one_div_prime_atTop
  -- Therefore 1 + sum diverges
  have h_one_add_sum_unbounded :
      Tendsto (fun k => 1 + ∑ p ∈ Finset.filter Nat.Prime (Finset.range k), 1 / (p : ℝ))
        atTop atTop := by
    exact tendsto_atTop_add_const_left atTop 1 h_sum_unbounded
  -- By lower bound, product diverges
  exact tendsto_atTop_mono h_lower_bound h_one_add_sum_unbounded

/-- Squarish iterates are eventually absent: for n ≥ 2, σₖ(n) is not squarish
    for all sufficiently large k.
    
    This uses Zsygmondy's theorem on primitive prime divisors of 2^a - 1
    to show that consecutive squarish iterates are impossible for large enough a.
    See proofs/prime-persistence.md, Theorem 1. -/
lemma squarish_iterates_finite (n : ℕ) (hn : n ≥ 2) :
    ∃ K, ∀ k ≥ K, ¬IsSquarish ((sigma 1)^[k] n) := by
  sorry

/-- For n ≥ 2, the prime 2 eventually always divides σₖ(n).
    
    Proof: By `squarish_iterates_finite`, eventually σₖ(n) is not squarish.
    By `sigma_even_of_not_squarish`, σ(m) is even when m is not squarish.
    So σₖ₊₁(n) = σ(σₖ(n)) is even for large k. -/
lemma prime_persistence_two (n : ℕ) (hn : n ≥ 2) :
    ∃ K, ∀ k ≥ K, 2 ∣ (sigma 1)^[k] n := by
  obtain ⟨K, hK⟩ := squarish_iterates_finite n hn
  use K + 1
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hnsq : ¬IsSquarish ((sigma 1)^[j] n) := hK j (by omega)
  have hne : (sigma 1)^[j] n ≠ 0 := by
    have := sigma_iterate_ge_two n hn j; omega
  have heven := sigma_even_of_not_squarish hne hnsq
  simp only [Function.iterate_succ', Function.comp_apply]
  exact even_iff_two_dvd.mp heven

/-! ### Helper lemmas for odd prime persistence

The proof of odd prime persistence uses the following chain:
1. `v2_hits_residue` — the 2-adic valuation of σₖ(n) hits every residue class mod d
2. `q_dvd_sigma_two_pow_iff` — connects divisibility by q to multiplicative order
3. `q_dvd_sigma_of_v2_dvd` — if q | σ(2^{v₂(m)}), then q | σ(m)
4. `prime_enters_infinitely` — q enters the orbit infinitely often (from 1-3)
5. `prime_div_eventually_always` — infinitely often → eventually always
-/

/-- (2 : ZMod q) ≠ 0 for odd prime q. -/
lemma two_ne_zero_zmod (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    (2 : ZMod q) ≠ 0 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have : (2 : ZMod q) = ((2 : ℕ) : ZMod q) := by norm_cast
  rw [this, Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  exact hodd (Nat.le_of_dvd (by omega) hdvd |>.antisymm hq.two_le)

/-- The multiplicative order of 2 in (ZMod q) is at least 1 for prime q ≠ 2.
    Uses Fermat's little theorem: 2^(q-1) ≡ 1 (mod q). -/
lemma orderOf_two_zmod_pos (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    orderOf (2 : ZMod q) ≥ 1 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have h2ne := two_ne_zero_zmod q hq hodd
  have hfermat : (2 : ZMod q) ^ (q - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  have hdvd := orderOf_dvd_of_pow_eq_one hfermat
  exact Nat.pos_of_ne_zero fun h0 =>
    (by have := hq.two_le; omega : q - 1 ≠ 0) (Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd))

/-- q ∣ 2^n - 1 iff (2 : ZMod q)^n = 1.
    This bridges between natural number divisibility and ZMod arithmetic. -/
lemma dvd_two_pow_sub_one_iff (q n : ℕ) :
    q ∣ 2 ^ n - 1 ↔ (2 : ZMod q) ^ n = 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow n 2 (by omega))]
  simp [sub_eq_zero]

/-- q ∣ σ(2^a) iff ord_q(2) ∣ (a + 1).
    Since σ(2^a) = 2^(a+1) - 1, this reduces to the order condition. -/
lemma q_dvd_sigma_two_pow_iff (q a : ℕ) :
    q ∣ sigma 1 (2 ^ a) ↔ orderOf (2 : ZMod q) ∣ (a + 1) := by
  rw [sigma_pow_two', dvd_two_pow_sub_one_iff]
  exact orderOf_dvd_iff_pow_eq_one.symm

/-- 2^{v₂(m)} divides m. -/
lemma two_pow_factorization_dvd (m : ℕ) (hm : m ≠ 0) : 2 ^ (m.factorization 2) ∣ m :=
  (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm).mpr le_rfl

/-- The odd part m / 2^{v₂(m)} is odd (by maximality of v₂). -/
lemma odd_part_is_odd (m : ℕ) (hm : m ≠ 0) :
    Odd (m / 2 ^ (m.factorization 2)) := by
  by_contra h; rw [Nat.not_odd_iff_even] at h
  obtain ⟨c, hc⟩ := h
  exact Nat.pow_succ_factorization_not_dvd hm Nat.prime_two (by
    rw [pow_succ]; exact Nat.mul_dvd_of_dvd_div
      (two_pow_factorization_dvd m hm) ⟨c, by omega⟩)

/-- If q ∣ σ(2^{v₂(m)}), then q ∣ σ(m).
    Uses multiplicativity: σ(m) = σ(2^a) · σ(t) where m = 2^a · t, t odd. -/
lemma q_dvd_sigma_of_v2_dvd (q m : ℕ) (hm : m ≠ 0)
    (hq : q ∣ sigma 1 (2 ^ (m.factorization 2))) :
    q ∣ sigma 1 m := by
  conv_rhs => rw [show m = 2 ^ (m.factorization 2) * (m / 2 ^ (m.factorization 2)) from
    (Nat.mul_div_cancel' (two_pow_factorization_dvd m hm)).symm]
  rw [isMultiplicative_sigma.map_mul_of_coprime
    (Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (odd_part_is_odd m hm)))]
  exact dvd_mul_of_dvd_left hq _

/-- The 2-adic valuation of σₖ(n) hits multiples of any d ≥ 1 infinitely often.
    
    Precisely: for any d ≥ 1 and K, there exists k ≥ K such that
    d ∣ (v₂(σₖ(n)) + 1). This is the key number-theoretic input for
    showing that odd primes enter the orbit.
    
    The proof uses the Escape Lemma (S* is infinite) together with
    Dirichlet's theorem on primes in arithmetic progressions to show
    that v₂(σₖ(n)) is unbounded and hits all residue classes.
    See proofs/prime-persistence.md, Lemma 5 and Corollary 5.1. -/
lemma v2_hits_residue (n : ℕ) (hn : n ≥ 2) (d : ℕ) (hd : d ≥ 1) :
    ∀ K, ∃ k ≥ K, d ∣ ((sigma 1)^[k] n).factorization 2 + 1 := by
  sorry

/-- Once a prime q divides σₖ(n) for infinitely many k, it eventually always divides.
    This is the "persistence" step: once q enters, exits become impossible.
    
    The argument uses: when q ∣ σₖ(n), write σₖ(n) = q^b · M with gcd(M,q) = 1.
    Then σ(q^b) ≡ 1 (mod q), so q ∣ σₖ₊₁(n) iff q ∣ σ(M).
    The growing number of prime factors of M ensures q ∣ σ(M) eventually.
    See proofs/prime-persistence.md, Theorem 2, Stage 2. -/
lemma prime_div_eventually_always (q : ℕ) (hq : Nat.Prime q) (n : ℕ) (hn : n ≥ 2)
    (hinf : ∀ K, ∃ k ≥ K, q ∣ (sigma 1)^[k] n) :
    ∃ K, ∀ k ≥ K, q ∣ (sigma 1)^[k] n := by
  sorry

/-- For odd prime q, q divides σₖ(n) for infinitely many k.
    
    Proof: Let d = ord_q(2). By `v2_hits_residue`, there are infinitely many k
    with d ∣ (v₂(σₖ(n)) + 1). For such k, q ∣ σ(2^{v₂(σₖ(n))}) by
    `q_dvd_sigma_two_pow_iff`, and then q ∣ σ(σₖ(n)) = σₖ₊₁(n) by
    `q_dvd_sigma_of_v2_dvd`. -/
lemma prime_enters_infinitely (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2)
    (n : ℕ) (hn : n ≥ 2) :
    ∀ K, ∃ k ≥ K, q ∣ (sigma 1)^[k] n := by
  intro K
  obtain ⟨k, hk_ge, hd_dvd⟩ := v2_hits_residue n hn
    (orderOf (2 : ZMod q)) (orderOf_two_zmod_pos q hq hodd) K
  have hne : (sigma 1)^[k] n ≠ 0 := by
    have := sigma_iterate_ge_two n hn k; omega
  exact ⟨k + 1, by omega, by
    simp only [Function.iterate_succ', Function.comp_apply]
    exact q_dvd_sigma_of_v2_dvd q _ hne ((q_dvd_sigma_two_pow_iff q _).mpr hd_dvd)⟩

/-- For odd prime q, q eventually always divides σₖ(n).
    
    Combines `prime_enters_infinitely` (q enters infinitely often)
    with `prime_div_eventually_always` (infinitely often → eventually always). -/
lemma prime_persistence_odd (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2)
    (n : ℕ) (hn : n ≥ 2) :
    ∃ K, ∀ k ≥ K, q ∣ (sigma 1)^[k] n := by
  exact prime_div_eventually_always q hq n hn (prime_enters_infinitely q hq hodd n hn)

/-- **Prime Persistence**: Every prime eventually always divides σₖ(n).
    
    For any prime q and n ≥ 2, there exists K such that q ∣ σₖ(n) for all k ≥ K.
    
    The proof splits into two cases:
    - For q = 2: Uses `prime_persistence_two` (squarish iterates are finite).
    - For odd q: Uses `prime_persistence_odd` (2-adic valuation mechanism).
    
    See proofs/prime-persistence.md for the full natural language proof. -/
lemma prime_persistence (q : ℕ) (hq : Nat.Prime q) (n : ℕ) (hn : n ≥ 2) :
    ∃ K, ∀ k ≥ K, q ∣ (sigma 1)^[k] n := by
  rcases Nat.Prime.eq_two_or_odd hq with rfl | hodd
  · exact prime_persistence_two n hn
  · exact prime_persistence_odd q hq (by omega) n hn

/-- The sum of reciprocals of primes in sigma orbit tends to infinity.
    This is the key lemma for proving Erdős Problem 410.
    
    Proof: By Prime Persistence, every prime eventually permanently divides σₖ(n).
    For any target R, choose M primes whose reciprocal sum exceeds R.
    Take K = max of their persistence thresholds. For k ≥ K, all M primes
    are in σₖ(n)'s prime factors, so the sum exceeds R. -/
lemma prime_factors_accumulate (n : ℕ) (hn : n ≥ 2) :
    Tendsto (fun k => ∑ p ∈ ((sigma 1)^[k] n).primeFactors, (1 / (p : ℝ))) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro R
  -- Step 1: The sum of prime reciprocals diverges
  have h_primes_diverge := Theorems100.Real.tendsto_sum_one_div_prime_atTop
  rw [tendsto_atTop_atTop] at h_primes_diverge
  obtain ⟨N, hN⟩ := h_primes_diverge R
  
  -- Step 2: The set S = {p < N : Prime p} has reciprocal sum ≥ R
  let S := Finset.filter Nat.Prime (Finset.range N)
  have hS_sum : R ≤ ∑ p ∈ S, (1 : ℝ) / p := hN N le_rfl
  
  -- Step 3: For each prime p in S, get persistence threshold
  have h_persist : ∀ p ∈ S, ∃ K, ∀ k ≥ K, p ∣ (sigma 1)^[k] n := fun p hp => by
    have hp_prime : Nat.Prime p := Finset.mem_filter.mp hp |>.2
    exact prime_persistence p hp_prime n hn
  
  -- Step 4: Choose thresholds for all primes in S
  classical
  choose! K_of hK_of using h_persist
  
  -- Step 5: Take K = max of all thresholds (or 0 if S is empty)
  let K := if hne : S.Nonempty then S.sup' hne K_of else 0
  use K
  
  intro k hk
  -- For k ≥ K, every prime in S divides σₖ(n)
  have h_div : ∀ p ∈ S, p ∣ (sigma 1)^[k] n := fun p hp => by
    have hKp : K_of p ≤ K := by
      simp only [K]
      split_ifs with hne
      · exact Finset.le_sup' K_of hp
      · exfalso; exact hne ⟨p, hp⟩
    exact hK_of p hp k (le_trans hKp hk)
  
  -- σₖ(n) ≠ 0
  have hsk_ne : (sigma 1)^[k] n ≠ 0 := by
    have h2 := sigma_iterate_ge_two n hn k
    omega
  
  -- Every prime in S is in the prime factors of σₖ(n)
  have h_mem : S ⊆ ((sigma 1)^[k] n).primeFactors := fun p hp => by
    have hp_prime : Nat.Prime p := Finset.mem_filter.mp hp |>.2
    exact Nat.mem_primeFactors.mpr ⟨hp_prime, h_div p hp, hsk_ne⟩
  
  -- Sum over S ≤ sum over primeFactors (since 1/p ≥ 0)
  have h_nonneg : ∀ p ∈ ((sigma 1)^[k] n).primeFactors, p ∉ S → (0 : ℝ) ≤ 1 / p := 
    fun p _ _ => by positivity
  
  calc R ≤ ∑ p ∈ S, (1 : ℝ) / p := hS_sum
    _ ≤ ∑ p ∈ ((sigma 1)^[k] n).primeFactors, (1 : ℝ) / p := 
        Finset.sum_le_sum_of_subset_of_nonneg h_mem h_nonneg

/-- The abundancy ratio σ(σₖ(n))/σₖ(n) tends to infinity. -/
lemma abundancy_ratio_diverges (n : ℕ) (hn : n ≥ 2) :
    Tendsto (fun k => (sigma 1 ((sigma 1)^[k] n) : ℝ) / ((sigma 1)^[k] n : ℝ)) atTop atTop := by
  have h_acc := prime_factors_accumulate n hn
  rw [tendsto_atTop_atTop] at h_acc ⊢
  intro b
  obtain ⟨k₀, hk₀⟩ := h_acc (b - 1)
  use k₀
  intro k hk
  have h_sum := hk₀ k hk
  have h_bound := abundancy_prime_factor_bound ((sigma 1)^[k] n) (by
    have h2 : (sigma 1)^[k] n ≥ 2 := sigma_iterate_ge_two n hn k
    omega)
  calc (sigma 1 ((sigma 1)^[k] n) : ℝ) / ((sigma 1)^[k] n : ℝ)
      ≥ ∏ p ∈ ((sigma 1)^[k] n).primeFactors, (1 + 1 / (p : ℝ)) := h_bound
    _ ≥ 1 + ∑ p ∈ ((sigma 1)^[k] n).primeFactors, (1 / (p : ℝ)) := by
      apply prod_one_add_ge_one_add_sum
      intro p _
      positivity
    _ ≥ 1 + (b - 1) := by linarith
    _ = b := by linarith

/-! ## Super-Exponential Lower Bound

The main theorem `erdos_410` requires showing that σₖ(n)^{1/k} → ∞,
which is equivalent to: for any c > 0, eventually c^k < σₖ(n).
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

/-- For c > 1, eventually c^k < σₖ(n).
Follows from `abundancy_ratio_diverges`. -/
lemma sigma_iterate_superexp_gt_one (n : ℕ) (hn : n ≥ 2) (c : ℝ) (hc : c > 1) :
    ∃ k₀, ∀ k ≥ k₀, c ^ k < ((sigma 1)^[k] n : ℝ) := by
  have hc_pos : c > 0 := by linarith
  have h_ratio := abundancy_ratio_diverges n hn
  rw [tendsto_atTop] at h_ratio
  have h2c := h_ratio (2 * c)
  rw [eventually_atTop] at h2c
  obtain ⟨k₁, hk₁⟩ := h2c
  have key : ∀ m : ℕ, ((sigma 1)^[k₁ + m] n : ℝ) ≥ (2 * c)^m * ((sigma 1)^[k₁] n : ℝ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hstep : (sigma 1)^[k₁ + (m + 1)] n = sigma 1 ((sigma 1)^[k₁ + m] n) := by
        simp only [show k₁ + (m + 1) = (k₁ + m) + 1 by omega,
          Function.iterate_succ', Function.comp_apply]
      rw [hstep]
      have hratio := hk₁ (k₁ + m) (by omega)
      have hpos : ((sigma 1)^[k₁ + m] n : ℝ) > 0 := by
        have := sigma_iterate_ge_two n hn (k₁ + m); positivity
      calc (sigma 1 ((sigma 1)^[k₁ + m] n) : ℝ)
          ≥ (2 * c) * ((sigma 1)^[k₁ + m] n : ℝ) := by
            have h := le_div_iff₀ hpos |>.mp hratio; linarith
        _ ≥ (2 * c) * ((2 * c)^m * ((sigma 1)^[k₁] n : ℝ)) :=
            mul_le_mul_of_nonneg_left ih (by linarith : 2 * c ≥ 0)
        _ = (2 * c)^(m+1) * ((sigma 1)^[k₁] n : ℝ) := by ring
  have hbase : ((sigma 1)^[k₁] n : ℝ) ≥ 2 := by exact_mod_cast sigma_iterate_ge_two n hn k₁
  have hlog : ∃ k₂ : ℕ, (2 : ℝ)^(k₂ + 1) > c^k₁ := by
    have htend := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (2:ℝ) > 1)
    rw [tendsto_atTop] at htend
    have h := htend (c^k₁ + 1)
    rw [eventually_atTop] at h
    obtain ⟨N, hN⟩ := h
    use N; have := hN (N + 1) (by omega); linarith
  obtain ⟨k₂, hk₂⟩ := hlog
  use k₁ + k₂ + 1
  intro k hk
  have hm : k - k₁ ≥ k₂ + 1 := by omega
  have h := key (k - k₁)
  rw [show k₁ + (k - k₁) = k by omega] at h
  have step1 : ((sigma 1)^[k] n : ℝ) ≥ (2 * c)^(k - k₁) * 2 :=
    calc ((sigma 1)^[k] n : ℝ) ≥ (2 * c)^(k - k₁) * ((sigma 1)^[k₁] n : ℝ) := h
      _ ≥ (2 * c)^(k - k₁) * 2 :=
          mul_le_mul_of_nonneg_left hbase (pow_nonneg (by linarith) _)
  have step2 : (2 * c)^(k - k₁) * 2 = (2 : ℝ)^(k - k₁ + 1) * c^(k - k₁) := by
    rw [mul_pow]; ring
  have step3 : (2 : ℝ)^(k - k₁ + 1) ≥ 2^(k₂ + 2) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have step4 : (2 : ℝ)^(k₂ + 2) > c^k₁ := by
    have h1 : (2 : ℝ)^(k₂ + 2) = 2 * 2^(k₂ + 1) := by ring
    have h2 : (2 : ℝ)^(k₂ + 1) > c^k₁ := hk₂
    have h3 : (2 : ℝ)^(k₂ + 1) > 0 := by positivity
    linarith
  calc c^k = c^k₁ * c^(k - k₁) := by rw [← pow_add]; congr; omega
    _ < 2^(k₂ + 2) * c^(k - k₁) :=
        mul_lt_mul_of_pos_right step4 (pow_pos hc_pos _)
    _ ≤ 2^(k - k₁ + 1) * c^(k - k₁) :=
        mul_le_mul_of_nonneg_right step3 (pow_nonneg (le_of_lt hc_pos) _)
    _ = (2 * c)^(k - k₁) * 2 := step2.symm
    _ ≤ ((sigma 1)^[k] n : ℝ) := step1

/-- Combined super-exponential bound for any c > 0.
Proven for c ≤ 1; the case c > 1 requires `sigma_iterate_superexp_gt_one`. -/
lemma sigma_iterate_superexp (n : ℕ) (hn : n ≥ 2) (c : ℝ) (hc : c > 0) :
    ∃ k₀, ∀ k ≥ k₀, c ^ k < ((sigma 1)^[k] n : ℝ) := by
  rcases le_or_gt c 1 with hle | hgt
  · exact sigma_iterate_superexp_le_one n hn c hc hle
  · exact sigma_iterate_superexp_gt_one n hn c hgt

/-- c^k < x implies c < x^{1/k} for k ≥ 1, c > 0, x > 0 -/
lemma lt_rpow_inv_of_pow_lt {c x : ℝ} {k : ℕ} (hc : c > 0) (hx : x > 0) (hk : k ≥ 1)
    (h : c ^ k < x) : c < x ^ (1 / (k : ℝ)) := by
  have hk_pos : (k : ℝ) > 0 := by positivity
  have h1div : (1 : ℝ) / (k : ℝ) = ((k : ℝ))⁻¹ := one_div (k : ℝ)
  rw [h1div, Real.lt_rpow_inv_iff_of_pos (le_of_lt hc) (le_of_lt hx) hk_pos]
  rw [Real.rpow_natCast]
  exact h

/-- Erdős Problem 410: Iterated sum-of-divisors grows super-exponentially. -/
theorem erdos_410 : ∀ n > 1,
    Tendsto (fun k : ℕ ↦ ((sigma 1)^[k] n : ℝ) ^ (1 / (k : ℝ))) atTop atTop := by
  intro n hn
  rw [tendsto_atTop]
  intro B
  by_cases hB : B ≤ 0
  · filter_upwards [eventually_ge_atTop 1] with k hk
    have hge2 := sigma_iterate_ge_two n (by omega) k
    have hpos : (0:ℝ) < ((sigma 1)^[k] n : ℝ) := by positivity
    have := Real.rpow_pos_of_pos hpos (1 / k)
    linarith
  · push_neg at hB
    have hcpos : max B 2 > 0 := by positivity
    obtain ⟨k₀, hk₀⟩ := sigma_iterate_superexp n (by omega) (max B 2) hcpos
    filter_upwards [eventually_ge_atTop (max k₀ 1)] with k hk
    have hk_ge_1 : k ≥ 1 := le_max_right k₀ 1 |>.trans hk
    have hk_ge_k₀ : k ≥ k₀ := le_max_left k₀ 1 |>.trans hk
    have hf_bound := hk₀ k hk_ge_k₀
    have hf_pos : (0:ℝ) < ((sigma 1)^[k] n : ℝ) := by
      have := sigma_iterate_ge_two n (by omega) k; positivity
    have h1 := lt_rpow_inv_of_pow_lt hcpos hf_pos hk_ge_1 hf_bound
    linarith [le_max_left B 2]

end Erdos410
