import Mathlib

open ArithmeticFunction

def check (limit : ℕ) : IO Unit := do
  for m in [1:limit] do
    let n := m * m
    let s := sigma 1 n
    let sqrt := (Float.sqrt (s.toFloat)).toUInt64.toNat
    if sqrt * sqrt == s then
      IO.println s!"Counterexample found: m={m}, n={n}, sigma={s} = {sqrt}^2"
  IO.println "Check complete."

#eval check 1000
