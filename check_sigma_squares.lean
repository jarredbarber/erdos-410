import Mathlib

open ArithmeticFunction

def check (limit : ℕ) : IO Unit := do
  for k in [1:limit] do
    let n := 2 * k * k
    let s := sigma 1 n
    let sqrt := (Float.sqrt (s.toFloat)).toUInt64.toNat
    if sqrt * sqrt == s then
      IO.println s!"Counterexample found: k={k}, n={n}, sigma={s} = {sqrt}^2"
      return
  IO.println "No counterexamples found."

#eval check 1000
