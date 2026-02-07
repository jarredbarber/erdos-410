# CLAUDE.md

## Project Overview

This project aims to prove **Erdős Problem #410** using Lean 4 and Mathlib.

**Problem:** Let $\sigma_1(n) = \sigma(n)$ (sum of divisors) and $\sigma_k(n) = \sigma(\sigma_{k-1}(n))$. Prove that for all $n \geq 2$, $\lim_{k \to \infty} \sigma_k(n)^{1/k} = \infty$.

**Formal statement:** `Erdos/Basic.lean` → `erdos_410`

See `problem.md` for full context, references, and background.

## ⚠️ CRITICAL: Immutable Theorem Statement

The theorem `erdos_410` in `Erdos/Basic.lean` is the **canonical problem definition** and **MUST NOT be modified under any circumstances**.

- Do NOT change the type signature, hypotheses, or conclusion
- Do NOT weaken assumptions or strengthen conclusions
- Do NOT add axioms to make the proof easier
- Do NOT replace it with an equivalent-but-different formulation
- If the statement appears unprovable as written, **escalate to the advisor**

All proof work (helper lemmas, intermediate results, tactic scripts) must ultimately discharge the `sorry` in `erdos_410` without altering its statement.

## Commands

```bash
lake build              # Build the project (typecheck all proofs)
lake build Erdos        # Build just our module
```

## Project Structure

```
Erdos/
  Basic.lean            # Main theorem statement (IMMUTABLE) + proof
lakefile.toml           # Lean 4 project config (Mathlib dependency)
lean-toolchain          # Lean version (v4.27.0)
problem.md              # Problem description, references, context
```

## Lean Version

- **Lean:** v4.27.0
- **Mathlib:** v4.27.0

## Proof Strategy

Proofs should be organized as lemmas in `Erdos/` that build toward the main result. Use Mathlib's existing API for:

- `ArithmeticFunction.sigma` — sum of divisors
- `Function.iterate` — function iteration (`f^[k]`)
- `Filter.Tendsto` / `Filter.atTop` — limits and divergence

## Code Style

- 2-space indentation for Lean files
- Use `by` tactic blocks for proofs
- Name lemmas descriptively (e.g., `sigma_iterate_lower_bound`)
- Add doc comments to all non-trivial lemmas
