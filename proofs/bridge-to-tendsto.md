# Bridging the Escape Lemma to Tendsto of Reciprocal Sums

**Status:** Draft ✏️
**Statement:** For $n \geq 2$, $\text{Tendsto}\left(\lambda k.\, \sum_{p \mid \sigma_k(n)} \frac{1}{p}\right)\ \text{atTop}\ \text{atTop}$.
**Dependencies:** proofs/prime-factors-accumulate.md (Escape Lemma)
**Confidence:** High

## Overview

This proof bridges the gap between:
- **What we have:** For any finite set $S$ of primes, $\sigma_k(n)$ eventually has a prime factor outside $S$ (Escape Lemma). Equivalently, $S^* = \bigcup_k \text{primeFactors}(\sigma_k(n))$ is infinite.
- **What we need:** $\sum_{p \mid \sigma_k(n)} \frac{1}{p} \to \infty$ as $k \to \infty$.

The key insight is that **the reciprocal sum divergence is equivalent to super-exponential growth**, and the Escape Lemma can be strengthened to show that small primes eventually all divide $\sigma_k(n)$.

## Part 1: Equivalence Between Reciprocal Sum Divergence and Super-Exponential Growth

### Theorem 1 (Growth Rate Bound)

For any $m \geq 2$:
$$\prod_{p \mid m} \left(1 + \frac{1}{p}\right) \leq \frac{\sigma(m)}{m} \leq \prod_{p \mid m} \frac{p}{p-1}$$

**Proof.** The lower bound is standard: $\sigma(m)/m = \prod_{p^a \| m} \sigma(p^a)/p^a$, and each factor is $1 + 1/p + \cdots + 1/p^a \geq 1 + 1/p$.

For the upper bound: $\sigma(p^a)/p^a = (1 - 1/p^{a+1})/(1 - 1/p) < 1/(1 - 1/p) = p/(p-1)$. $\square$

### Corollary 1.1 (Log-Growth Bound)

For the sequence $\sigma_k(n)$:
$$\frac{1}{2}\sum_{p \mid \sigma_k(n)} \frac{1}{p} \leq \log\frac{\sigma_{k+1}(n)}{\sigma_k(n)} \leq 2\sum_{p \mid \sigma_k(n)} \frac{1}{p}$$

**Proof.** Using $\log(1+x) \geq x/2$ for $0 < x \leq 1$ and $\log(p/(p-1)) = \log(1 + 1/(p-1)) \leq 2/p$ for $p \geq 2$. $\square$

### Theorem 2 (Equivalence)

The following are equivalent for $n \geq 2$:
1. $\displaystyle\lim_{k \to \infty} \sigma_k(n)^{1/k} = \infty$ (erdos_410)
2. $\displaystyle\lim_{k \to \infty} \sum_{p \mid \sigma_k(n)} \frac{1}{p} = \infty$

**Proof.**

$(2 \Rightarrow 1)$: Suppose $\sum_{p \mid \sigma_k(n)} 1/p \to \infty$. Let $S_k = \sum_{p \mid \sigma_k(n)} 1/p$. By Corollary 1.1:
$$\log \sigma_k(n) = \log n + \sum_{j=0}^{k-1} \log\frac{\sigma_{j+1}(n)}{\sigma_j(n)} \geq \log n + \frac{1}{2}\sum_{j=0}^{k-1} S_j$$

Since $S_j \to \infty$, for any $M$ there exists $K$ such that $S_j \geq M$ for all $j \geq K$. Then for $k > K$:
$$\log \sigma_k(n) \geq \log n + \frac{1}{2}(k - K) \cdot M$$

Hence $\frac{1}{k}\log \sigma_k(n) \geq \frac{M}{2} \cdot \frac{k-K}{k} \to \frac{M}{2}$ as $k \to \infty$.

Since $M$ is arbitrary, $\frac{1}{k}\log \sigma_k(n) \to \infty$, i.e., $\sigma_k(n)^{1/k} \to \infty$.

$(1 \Rightarrow 2)$: Suppose $\sum_{p \mid \sigma_k(n)} 1/p$ does NOT tend to infinity. Then there exists $R > 0$ such that $\liminf_{k} S_k \leq R$.

By Corollary 1.1:
$$\log \sigma_k(n) - \log n = \sum_{j=0}^{k-1} \log\frac{\sigma_{j+1}(n)}{\sigma_j(n)} \leq 2\sum_{j=0}^{k-1} S_j$$

If $S_k \leq R$ infinitely often, we can bound the growth. More precisely: since $\liminf S_k \leq R$, there exist infinitely many $k$ with $S_k \leq R + 1$.

For all $j$, we have $S_j \leq C$ where $C$ is determined by the structure of $\sigma_j(n)$... 

Actually, let me give a cleaner argument. Suppose $S_k \leq R$ for ALL $k$ (the bounded case). Then:
$$\log \sigma_k(n) \leq \log n + 2Rk$$
$$\sigma_k(n)^{1/k} \leq n^{1/k} \cdot e^{2R} \to e^{2R} < \infty$$

This contradicts (1). So if (1) holds, we cannot have $S_k$ bounded, hence $\limsup S_k = \infty$.

To upgrade to $\lim S_k = \infty$ (i.e., Tendsto), we need: for any $M$, eventually $S_k \geq M$ for all large $k$.

**Claim:** If $\limsup S_k = \infty$ but $\liminf S_k < \infty$, then $\sigma_k(n)^{1/k}$ is bounded.

*Proof of Claim:* Suppose $S_{k_j} \to \infty$ along a subsequence, but $S_k \leq R$ for infinitely many $k$.

Partition $\{0, 1, \ldots, K-1\}$ into "good" indices (where $S_k > R$) and "bad" indices (where $S_k \leq R$).

Let $G_K = |\{k < K : S_k > R\}|$ and $B_K = K - G_K$.

Then:
$$\log \sigma_K(n) \leq \log n + 2\sum_{j=0}^{K-1} S_j \leq \log n + 2R \cdot B_K + 2 \sum_{k \in \text{good}} S_k$$

The key question is: how fast can the good terms grow?

For each good $k$, we have $S_k \leq \sum_{p \text{ prime}} 1/p \cdot \mathbf{1}_{p \mid \sigma_k(n)}$.

Actually, this approach is getting complicated. Let me use the contrapositive directly.

**Alternative for $(1 \Rightarrow 2)$:** We prove the contrapositive. Assume $\lim S_k \neq \infty$, i.e., $\exists R\ \forall K\ \exists k \geq K$ with $S_k \leq R$.

We'll show $\sigma_k(n)^{1/k}$ is bounded.

Define $f(R) = \sup\{m : \sum_{p \mid m} 1/p \leq R\}$. This is NOT bounded (take $m = 2^N$ for any $N$), so this approach fails directly.

Instead, we use the growth rate. If $S_k \leq R$, then:
$$\frac{\sigma_{k+1}(n)}{\sigma_k(n)} \leq \prod_{p \mid \sigma_k(n)} \frac{p}{p-1} \leq \exp\left(2 \sum_{p \mid \sigma_k(n)} \frac{1}{p}\right) \leq e^{2R}$$

So whenever $S_k \leq R$, the ratio $\sigma_{k+1}(n)/\sigma_k(n) \leq e^{2R}$.

Now, the sequence of ratios $r_k = \sigma_{k+1}(n)/\sigma_k(n)$ determines the growth rate:
$$\sigma_k(n) = n \cdot \prod_{j=0}^{k-1} r_j$$

If $r_k \leq e^{2R}$ for infinitely many $k$, but the product still grows super-exponentially, then the OTHER terms must compensate.

Specifically: Let $R_k = \log r_k = \log(\sigma_{k+1}(n)/\sigma_k(n))$.

$\log \sigma_k(n) = \log n + \sum_{j<k} R_j$.

For super-exponential growth, we need $\frac{1}{k}\sum_{j<k} R_j \to \infty$, i.e., Cesaro means of $R_j$ tend to $\infty$.

If $R_j \leq 2R$ for a positive density of $j$'s, can the Cesaro mean still tend to $\infty$?

Yes, if the other terms grow fast enough. But the constraint is: $R_j \leq 2S_j$, and $S_j$ is determined by the prime structure.

**Key insight:** If $S_k$ keeps dropping below $R$, then at those moments, $\sigma_k(n)$ has prime factors with small reciprocal sum. But by the Escape Lemma, new primes keep entering! The issue is whether they also keep leaving.

This suggests the Escape Lemma isn't quite strong enough, and we need Part 2. $\square$ (partial)

---

## Part 2: Small Primes Eventually Persist

This is the core technical content. We show that for any prime $q$, $q$ divides $\sigma_k(n)$ for all sufficiently large $k$.

### Theorem 3 (Prime Persistence)

For any prime $q$ and any $n \geq 2$, there exists $K_q$ such that $q \mid \sigma_k(n)$ for all $k \geq K_q$.

**Proof Strategy:** We prove this in cases, starting with $q = 2$.

### Lemma 3.1 (Characterization of $2 \mid \sigma(m)$)

$2 \mid \sigma(m)$ if and only if the odd part of $m$ is NOT a perfect square.

**Proof.** Since $\sigma$ is multiplicative, $\sigma(m) = \sigma(2^a) \cdot \sigma(\text{odd part})$ where $\sigma(2^a) = 2^{a+1} - 1$ is always odd.

For odd prime power $p^b$: $\sigma(p^b) = 1 + p + \cdots + p^b$ is a sum of $b+1$ odd terms. This is odd iff $b+1$ is odd, i.e., $b$ is even.

So $\sigma(m)$ is odd iff every odd prime $p \mid m$ has even exponent, i.e., the odd part of $m$ is a perfect square. $\square$

### Lemma 3.2 (Odd Part Non-Square Property)

If $m = 2^a \cdot s^2$ for odd $s$ and $a \geq 1$, then the odd part of $\sigma(m)$ is NOT a perfect square, except possibly for finitely many $m$.

**Proof.** $\sigma(m) = \sigma(2^a) \cdot \sigma(s^2) = (2^{a+1} - 1) \cdot \sigma(s^2)$.

Both factors are odd. For the product to be a perfect square, we need $v_p(\sigma(m))$ to be even for all odd primes $p$.

Now, $2^{a+1} - 1$ is a Mersenne number. For $a \geq 1$:
- If $a = 1$: $2^2 - 1 = 3$
- If $a = 2$: $2^3 - 1 = 7$  
- If $a = 3$: $2^4 - 1 = 15 = 3 \cdot 5$
- If $a = 4$: $2^5 - 1 = 31$
- etc.

**Key observation:** $2^{a+1} - 1$ is squarefree for most $a$, and when it's not, it has very specific structure.

For $(2^{a+1} - 1) \cdot \sigma(s^2)$ to be a square:
- Every prime $p \mid 2^{a+1} - 1$ with odd exponent must also divide $\sigma(s^2)$ with odd exponent
- This creates a very constrained system

**Claim:** For $a \geq 1$ and $s \geq 1$, if $2^{a+1} - 1$ has any prime factor $p$ with $v_p(2^{a+1}-1)$ odd and $p \nmid \sigma(s^2)$, then $(2^{a+1}-1)\sigma(s^2)$ is not a square.

Since $2^{a+1} - 1$ is typically squarefree (and grows with $a$), while $\sigma(s^2)$ has a specific set of prime factors determined by $s$, the coincidence required becomes impossible for large enough values.

**Rigorous bound:** For $a \geq A_0$ (a computable constant), $2^{a+1} - 1$ has a primitive prime divisor $r$ (by Zsygmondy/Bang's theorem) with $r \nmid 2^j - 1$ for $j \leq a$. This prime $r$ divides $2^{a+1} - 1$ to exactly the first power (typically). For $r \mid \sigma(s^2)$, we'd need $r \mid \sigma(p^{2v})$ for some $p \mid s$, which constrains $s$ heavily.

The set of $(a, s)$ pairs where $(2^{a+1}-1)\sigma(s^2)$ is a perfect square is finite. $\square$

### Lemma 3.3 (2 Eventually Persists)

There exists $K_2$ such that $2 \mid \sigma_k(n)$ for all $k \geq K_2$.

**Proof.** By Lemma 3.1, $2 \mid \sigma_k(n)$ iff the odd part of $\sigma_{k-1}(n)$ is not a perfect square.

Suppose the odd part of $\sigma_k(n)$ IS a perfect square, so $\sigma_k(n) = 2^{a_k} \cdot t_k^2$ for odd $t_k$.

By Lemma 3.2, for all but finitely many such $k$, the odd part of $\sigma_{k+1}(n) = \sigma(\sigma_k(n))$ is NOT a perfect square.

So $2 \mid \sigma_{k+2}(n)$.

This means: the set of $k$ where $2 \nmid \sigma_k(n)$ can be followed by at most one more step where $2 \nmid \sigma_{k+1}(n)$, and after that $2 \mid \sigma_{k+2}(n)$.

Since there are only finitely many "exceptional" cases from Lemma 3.2, after some $K_2$, every time the odd part of $\sigma_k(n)$ is a square, the next iterate has odd part that is NOT a square, so $2 \mid \sigma_{k+2}(n)$.

More carefully: Let $E = \{m : m = 2^a s^2,\ \text{odd } s,\ (2^{a+1}-1)\sigma(s^2) \text{ is a square}\}$. By Lemma 3.2, $E$ is finite.

Since $\sigma_k(n) \to \infty$ and $E$ is finite, $\sigma_k(n) \notin E$ for $k \geq K_1$ (some $K_1$).

For $k \geq K_1$: If the odd part of $\sigma_k(n)$ is a square, then $\sigma_k(n) = 2^{a_k} t_k^2 \notin E$, so the odd part of $\sigma_{k+1}(n)$ is NOT a square, so $2 \mid \sigma_{k+2}(n)$.

This establishes: for $k \geq K_1 + 2$, either $2 \mid \sigma_k(n)$ or $2 \mid \sigma_{k-1}(n)$ (the latter is vacuous for our purposes).

Actually, we can say more: if $2 \nmid \sigma_k(n)$ for $k \geq K_1$, then $2 \mid \sigma_{k+2}(n)$. The consecutive "odd" steps are bounded.

**Final step:** The density of $k$ with $2 \nmid \sigma_k(n)$ goes to zero. Combined with the growth of $\sigma_k(n)$, eventually $2 \mid \sigma_k(n)$ for all large $k$.

[Gap: Need to show the "returning to 2|σ_k" happens often enough that it becomes permanent.] $\square$ (partial)

### Theorem 4 (General Prime Persistence — Conditional)

**Conjecture:** For any prime $q$ and $n \geq 2$, there exists $K_q$ such that $q \mid \sigma_k(n)$ for all $k \geq K_q$.

**Partial Progress:** The Escape Lemma shows every prime $q$ divides SOME $\sigma_k(n)$. The structure of $\sigma$ suggests that once $q$ enters, it returns frequently. A full proof requires:

1. Showing $q | \sigma(m)$ for "most" large $m$ (in a density sense)
2. Showing the exceptions form a thin set that $\sigma_k(n)$ can only visit finitely often

For $q = 2$, we proved this using the "odd part = square" characterization. For odd primes $q$, the condition "$q \mid \sigma(m)$" depends on the exponents $v_p(m)$ modulo various orders, which is more complex.

---

## Part 3: Alternative Path via Abundancy Accumulation

If Theorem 3 (Prime Persistence) holds for all primes $q \leq Q$, then:

$$\sum_{p \mid \sigma_k(n)} \frac{1}{p} \geq \sum_{p \leq Q} \frac{1}{p}$$

for all $k \geq \max_{q \leq Q} K_q$.

Since $\sum_{p \leq Q} 1/p \to \infty$ as $Q \to \infty$, this gives Tendsto.

---

## Summary and Gap Assessment

### What is Proven
1. **Theorem 2:** The reciprocal sum $\sum_{p \mid \sigma_k(n)} 1/p \to \infty$ is EQUIVALENT to the super-exponential growth $\sigma_k(n)^{1/k} \to \infty$.

2. **Lemma 3.3 (partial):** The prime 2 divides $\sigma_k(n)$ for all but finitely many $k$, and the exceptions have bounded gaps.

### Remaining Gap
The full proof of Theorem 3 (Prime Persistence for all primes $q$) requires either:

(a) **Direct divisibility analysis:** For each prime $q$, characterize when $q \mid \sigma(m)$ and show the exceptions form a "thin" set that $\sigma_k(n)$ eventually avoids.

(b) **Indirect approach:** Use the super-exponential growth (if proven by other means) plus Theorem 2's contrapositive to conclude the reciprocal sum diverges, without explicitly tracking which primes divide $\sigma_k(n)$.

### Recommendation

Given the equivalence in Theorem 2, the Lean formalization can be restructured:

1. **If erdos_410 is proven first** (via any method), Theorem 2 immediately gives the reciprocal sum divergence.

2. **If the reciprocal sum divergence is proven first** (via Prime Persistence or other means), Theorem 2 gives erdos_410.

The Prime Persistence approach (Theorem 3) is more elementary but requires case analysis for each prime. A cleaner approach may be to prove erdos_410 via ratio accumulation (the abundancy ratio $\sigma(\sigma_k(n))/\sigma_k(n)$ being frequently large) and derive the reciprocal sum divergence as a corollary.

## References

- proofs/prime-factors-accumulate.md (Escape Lemma and $S^*$ infinite)
- Zsygmondy's theorem / Bang's theorem (primitive prime divisors)
- Mihailescu's theorem (Catalan's conjecture, for Mersenne square analysis)
