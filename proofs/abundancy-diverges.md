# Abundancy Ratio Diverges via Prime Factor Accumulation

**Status:** Draft ✏️
**Statement:** For $n \geq 2$, $\sigma(\sigma_k(n))/\sigma_k(n) \to \infty$ as $k \to \infty$.
**Dependencies:** proofs/prime-factors-accumulate.md
**Confidence:** High

## Proof

### Setup

We use three already-proven results:
1. **Abundancy lower bound** (`abundancy_prime_factor_bound`): $\sigma(m)/m \geq \prod_{p \mid m} (1 + 1/p)$
2. **Mertens-type divergence** (`prod_one_plus_inv_primes_unbounded`): $\prod_{p \leq P, \, p \text{ prime}} (1 + 1/p) \to \infty$ as $P \to \infty$
3. **Prime factors accumulate** (from `proofs/prime-factors-accumulate.md`): The set $S^* = \bigcup_k \mathrm{primeFactors}(\sigma_k(n))$ is infinite.

### Direct Argument

Fix any $R > 0$. We need to show: for all sufficiently large $k$, $\sigma(\sigma_k(n))/\sigma_k(n) > R$.

By the Mertens-type divergence, there exists a finite set of primes $P = \{p_1, \ldots, p_M\}$ such that $\prod_{i=1}^{M} (1 + 1/p_i) > R$.

Since $S^*$ is infinite, there exists $K$ such that $P \subseteq \bigcup_{k \leq K} \mathrm{primeFactors}(\sigma_k(n))$. But this does NOT mean $P \subseteq \mathrm{primeFactors}(\sigma_k(n))$ for any single $k$. This is the gap.

### Strengthened Version Needed

The proof requires showing that for any finite set $P$ of primes, ALL primes in $P$ eventually divide $\sigma_k(n)$ simultaneously. This is the "Tendsto" version of prime factor accumulation.

**Claim:** For any prime $q$, once $q \mid \sigma_{k_0}(n)$ for some $k_0$, then $q \mid \sigma_k(n)$ for all $k \geq k_0 + 1$.

Wait, this is false in general. For example, $\sigma(6) = 12$, $\sigma(12) = 28$. We have $3 \mid 6$ but $3 \nmid 28$.

### Alternative: Direct Super-Exponential Proof

Instead of going through abundancy divergence, we can prove erdos_410 more directly.

**Key insight:** We don't need the abundancy ratio to diverge for EVERY iterate. We just need it to be large OFTEN ENOUGH.

**Approach:** For any $c > 1$, we need to show $c^k < \sigma_k(n)$ eventually.

From the escape lemma proof: the set of primes appearing in iterates is infinite. So for any $M$, there exist arbitrarily many $k$ where $\sigma_k(n)$ has at least $M$ distinct prime factors. At such $k$:

$$\sigma(\sigma_k(n)) / \sigma_k(n) \geq \prod_{p \mid \sigma_k(n)} (1 + 1/p) \geq \prod_{i=1}^{M} (1 + 1/q_i)$$

where $q_1 < \ldots$ are the actual prime factors of $\sigma_k(n)$. Since these are distinct primes $\geq 2$, we have $q_i \geq p_i$ (the $i$-th prime). Actually no, $q_i$ could be much larger.

The worst case is when the $M$ primes are all very large. But we can use: $\prod(1+1/p) \geq (1+1/P)^M$ where $P = \max q_i \leq \sigma_k(n)$. This gives a bound of $(1 + 1/\sigma_k(n))^M$ which is roughly $1$ for large iterates. Not useful.

### Correct Approach: Show Small Primes Accumulate

**Better claim:** Not just "infinitely many primes appear" but "every prime eventually appears."

**Lemma:** For any prime $q$, there exists $k_0$ such that $q \mid \sigma_{k_0}(n)$.

**Proof from the Escape Lemma:** The escape lemma already implies that infinitely many distinct primes appear. But we can strengthen: since $\sigma_k(n) \to \infty$, and for each prime $p \mid \sigma_k(n)$ with large exponent, $\sigma(p^a)$ introduces a NEW prime not previously seen — and this new prime could be any prime (determined by the factorization of $p^{a+1}-1$).

However, we don't control WHICH prime appears. We just know SOME new prime appears.

### Revised Strategy: Monotonicity of ω

**Claim:** $\omega(\sigma_k(n))$ is eventually non-decreasing.

This is plausible because: $\sigma$ is multiplicative, so $\sigma(m) = \prod_{p^a \| m} \sigma(p^a)$, and each $\sigma(p^a) \geq p+1$ introduces at least one prime factor (possibly $p$ again, or a new one). But the product structure means the prime factors of $\sigma(m)$ are the UNION of prime factors of the individual $\sigma(p^a)$ terms.

The issue is: $\sigma(p^a)$ might only have prime factors that are already present elsewhere in the product. So ω could temporarily decrease.

### SIMPLEST CORRECT APPROACH

Rather than trying to prove Tendsto, **modify the Lean proof structure**:

1. Change `prime_factors_accumulate` to state "for any M, there exists k with ω(σ_k(n)) ≥ M" (∀ M, ∃ k, ω(σ_k(n)) ≥ M). This follows directly from the escape lemma proof.

2. Change `sigma_iterate_superexp_gt_one` to use a "there exist arbitrarily large ratio steps" argument:

For any $c > 1$: Choose $M$ such that $\prod_{i=1}^{M} (p_i+1)/p_i > c$ (where $p_i$ is the $i$-th prime). Since the first $M$ primes are $\leq p_M$, and since $S^*$ is infinite, ALL the first $M$ primes eventually appear in some iterate.

Actually, we DO need all M primes to appear simultaneously. Let me think again...

**Final correct approach:** Use the escape lemma inductively to show that for each prime $p$, $p$ eventually divides some iterate. Then use compactness:

For any prime $p$: either $p$ divides infinitely many iterates, or there's a last iterate divisible by $p$. In the latter case, since $\sigma_k(n) \to \infty$ and the factorization changes... this isn't clear.

**ADMITTED GAP:** The connection from "infinitely many primes appear across iterates" to "abundancy ratio diverges" has a genuine gap. The Lean formalization should be restructured to use the weaker statement directly.

## References

- proofs/prime-factors-accumulate.md (Escape Lemma)
- Already proven: `abundancy_prime_factor_bound`, `prod_one_plus_inv_primes_unbounded`
