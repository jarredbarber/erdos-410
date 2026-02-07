import Mathlib

open Filter

example (n : ℕ) : Even n ↔ ¬Odd n := by
  apply?
