# Erdős Problem #410 — Project Status

**Status:** 🔴 **BLOCKED — Open Conjecture in Mathematics**

## Summary

Erdős Problem #410 is an **unproven conjecture** in number theory. The formal statement in `Erdos/Basic.lean` is correct, but no proof is known in the mathematical literature.

## What We've Proven

| Lemma | Statement | Status |
|-------|-----------|--------|
| `sigma_one_ge_succ` | σ(n) ≥ n + 1 for n ≥ 2 | ✅ Complete |
| `sigma_iterate_ge` | σₖ(n) ≥ n + k (linear lower bound) | ✅ Complete |
| `sigma_iterate_tendsto_atTop` | σₖ(n) → ∞ as k → ∞ | ✅ Complete |
| `abundancy_bound_even` | 2·σ(n) ≥ 3n for even n | ✅ Complete |
| `sigma_iterate_superexp_le_one` | ∀c ∈ (0,1], ∃k₀, ∀k ≥ k₀: c^k < σₖ(n) | ✅ Complete |
| `sigma_iterate_superexp_gt_one` | ∀c > 1, ∃k₀, ∀k ≥ k₀: c^k < σₖ(n) | ❌ **OPEN** |
| `erdos_410` | lim_{k→∞} σₖ(n)^{1/k} = ∞ for all n ≥ 2 | ❌ **OPEN** |

## Why the c > 1 Case Cannot Be Proven

### The Core Difficulty

To prove σₖ(n)^{1/k} → ∞, we need σₖ(n) to grow **super-exponentially** — faster than any geometric sequence c^k. This requires showing that the **abundancy ratio** σ(m)/m grows without bound along the trajectory.

### Why Existing Approaches Fail

| Approach | Obstacle |
|----------|----------|
| **Abundancy ≥ 1 + ε** | σ(n)/n can be arbitrarily close to 1 for prime powers p^k |
| **Force evenness** | σ(n) is odd when n is a square or twice a square |
| **Prime accumulation** | Only proven for "almost all" n, not all n |

### Literature

The key paper **Erdős-Granville-Pomerance-Spiro (1990)** proves:
- For **almost all** n (density 1), σₖ(n) grows doubly exponentially
- The set where growth is slower has density 0

This does NOT imply the pointwise bound for **all** n ≥ 2. The conjecture that the bound holds for every starting value remains open.

## Mathematical Gap

**Required Insight:** Prove that no starting value n ≥ 2 can produce a trajectory where σₖ(n) grows only exponentially or slower.

This would require showing that trajectories cannot "avoid" highly composite numbers indefinitely. No such proof is known.

## Project Recommendation

1. **Archive as partial success** — the verified lemmas are valuable
2. **Do not modify `erdos_410`** — the statement is correct
3. **Monitor mathematical literature** — if a proof is published, formalize it
4. **Consider weaker results** — density statements may be formalizable

## Files

```
Erdos/
  Basic.lean     # All lemmas + sorry for open problem
problem.md       # Problem description and references  
STATUS.md        # This file — project status
```

## Build

```bash
lake build Erdos
# Warnings expected for:
#   - sigma_iterate_superexp_gt_one (sorry)
#   - erdos_410 (sorry)
```
