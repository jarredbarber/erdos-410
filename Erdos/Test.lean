import Erdos.Basic

open ArithmeticFunction

namespace Erdos410

-- Helper 1
lemma sigma_two_mul_sq_not_squarish (k : ℕ) (hk : k ≥ 1) : ¬IsSquarish (sigma 1 (2 * k^2)) := by
  sorry

-- Helper 2
lemma sigma_sq_squarish_bound (m : ℕ) (hm : m > 11) : ¬IsSquarish (sigma 1 (m^2)) := by
  sorry

-- Check small cases
example : sigma 1 (1^2) = 1 := by native_decide -- Squarish
example : sigma 1 (3^2) = 13 := by native_decide -- Not Squarish
example : sigma 1 (9^2) = 121 := by native_decide -- Squarish (11^2)
example : sigma 1 (11^2) = 133 := by native_decide -- Not Squarish
example : sigma 1 (81) = 121 := by native_decide

end Erdos410
