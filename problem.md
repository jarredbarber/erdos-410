# Erdős Problem #410

**Status:** Open  
**Source:** [erdosproblems.com/410](https://www.erdosproblems.com/410)  
**Reference:** Erdős, Granville, Pomerance, Spiro — "On the normal behavior of the iterates of some arithmetical functions" (1990)  
**Tags:** number theory, iterated functions  
**OEIS:** [A007497](https://oeis.org/A007497)

## Problem Statement

Let $\sigma_1(n) = \sigma(n)$, the sum of divisors function, and $\sigma_k(n) = \sigma(\sigma_{k-1}(n))$.

Is it true that for all $n \geq 2$,

$$\lim_{k \to \infty} \sigma_k(n)^{1/k} = \infty?$$

## Formal Statement (Lean 4)

From the [Google DeepMind formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/410.lean) repository:

```lean
open ArithmeticFunction Filter

theorem erdos_410 : ∀ n > 1,
    Tendsto (fun k : ℕ ↦ ((sigma 1)^[k] n : ℝ) ^ (1 / (k : ℝ))) atTop atTop := by
  sorry
```

## Context

This is discussed in problem B9 of Guy's *Unsolved Problems in Number Theory* (2004).

The conjecture asks whether iterated application of the sum-of-divisors function grows super-exponentially — i.e., faster than any geometric sequence $c^k$ — for every starting value $n \geq 2$.
