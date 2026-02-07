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

/-- Erdős Problem 410: Iterated sum-of-divisors grows super-exponentially.

DO NOT MODIFY THIS STATEMENT. This is the canonical formalization from
google-deepmind/formal-conjectures. -/
@[reducible]
theorem erdos_410 : ∀ n > 1,
    Tendsto (fun k : ℕ ↦ ((sigma 1)^[k] n : ℝ) ^ (1 / (k : ℝ))) atTop atTop := by
  sorry

end Erdos410
