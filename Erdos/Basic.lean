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

/-- Erdős Problem 410: Iterated sum-of-divisors grows super-exponentially.

DO NOT MODIFY THIS STATEMENT. This is the canonical formalization from
google-deepmind/formal-conjectures. -/
theorem erdos_410 : ∀ n > 1,
    Tendsto (fun k : ℕ ↦ ((sigma 1)^[k] n : ℝ) ^ (1 / (k : ℝ))) atTop atTop := by
  sorry

end Erdos410
