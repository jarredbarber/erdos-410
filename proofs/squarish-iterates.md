# Eventually No Iterate Is Squarish

**Status:** Under review 🔍
**Statement:** For any $n \geq 2$, there exists $K$ such that $\sigma_k(n)$ is not squarish for all $k \geq K$.
**Dependencies:** proofs/prime-factors-accumulate.md (Escape Lemma, $\sigma_k(n) \to \infty$, $S^*$ infinite)
**Confidence:** High
**Reviewed by:** erdos410-9m4

---

## Overview

This proof establishes that for any starting point $n \geq 2$, the orbit under iterated $\sigma$ eventually escapes the set of squarish numbers and never returns. The proof is **orbit-specific**: it uses the dynamical structure of the particular sequence $\sigma_k(n)$, rather than global properties of the set {squarish numbers}.

**Key insight:** While the global set {$m$ not squarish : $\sigma(m)$ squarish} is infinite (containing all Mersenne primes, for instance), no individual orbit can hit squarish values infinitely often. The orbit's growth and prime accumulation properties prevent indefinite reentry into the squarish set.

---

## Preliminaries

### Definition 1 (Squarish)
A positive integer $m$ is **squarish** if its odd part is a perfect square. Equivalently:
$$m \text{ is squarish} \iff m = 2^a \cdot t^2 \text{ for some } a \geq 0 \text{ and odd } t \geq 1$$

**Examples:**
- Squarish: $1, 2, 4, 8, 9, 16, 18, 25, 32, 36, 49, 50, 72, \ldots$
- Not squarish: $3, 5, 6, 7, 10, 11, 12, 13, 14, 15, \ldots$

**Equivalent characterization:** $m$ is squarish iff every odd prime $p \mid m$ has even exponent $v_p(m)$.

### Lemma 1 (Parity Criterion for σ)
For any $m \geq 1$: $\sigma(m)$ is odd if and only if $m$ is squarish.

**Proof.** Since $\sigma$ is multiplicative:
$$\sigma(m) = \sigma(2^{v_2(m)}) \cdot \prod_{p \mid m,\, p \text{ odd}} \sigma(p^{v_p(m)})$$

**Factor 1:** $\sigma(2^a) = 1 + 2 + \cdots + 2^a = 2^{a+1} - 1$, which is always odd.

**Factor 2:** For odd prime $p$ and exponent $b$:
$$\sigma(p^b) = 1 + p + p^2 + \cdots + p^b$$
This is a sum of $b+1$ odd terms (since $p$ is odd, all powers of $p$ are odd).
- If $b$ is even: $b+1$ is odd, so $\sigma(p^b)$ is odd.
- If $b$ is odd: $b+1$ is even, so $\sigma(p^b)$ is even.

Therefore:
$$\sigma(m) \text{ is odd} \iff \text{every odd prime } p \mid m \text{ has even exponent } v_p(m) \iff m \text{ is squarish}$$
$\square$

### Corollary 1.1
$2 \mid \sigma(m)$ if and only if $m$ is not squarish.

### Lemma 2 (Zsygmondy's Theorem for Mersenne Numbers)
For $a \geq 7$, the Mersenne number $M_a = 2^a - 1$ has a **primitive prime divisor**: a prime $p$ such that $p \mid 2^a - 1$ but $p \nmid 2^j - 1$ for any $0 < j < a$.

**Proof.** This is Zsygmondy's theorem (1892). The only exceptions for $2^a - 1$ are:
- $a = 1$: $2^1 - 1 = 1$ (no prime divisors)
- $a = 6$: $2^6 - 1 = 63 = 7 \cdot 9$, but $7 \mid 2^3 - 1$

For all $a \geq 7$, primitive prime divisors exist. For $a \leq 6$, we handle these small cases separately. $\square$

**Note:** For a primitive prime $p$ of $2^a - 1$, we have $\mathrm{ord}_p(2) = a$ (the multiplicative order of 2 modulo $p$).

---

## Part 1: The Squarish Transition Set Is Finite

### Definition 2 (Transition Set)
The **squarish transition set** is:
$$T = \{m \in \mathbb{N} : m \text{ is squarish and } \sigma(m) \text{ is squarish}\}$$

### Theorem 1 (Transition Set Is Finite)
The set $T$ is finite.

**Proof.** Let $m = 2^a \cdot t^2$ be squarish, where $t \geq 1$ is odd.

Then:
$$\sigma(m) = \sigma(2^a) \cdot \sigma(t^2) = (2^{a+1} - 1) \cdot \sigma(t^2)$$

Since $2^{a+1} - 1$ is odd and $\sigma(t^2)$ is odd (by Lemma 1, since $t^2$ is a perfect square), the product $\sigma(m)$ is odd.

For $\sigma(m)$ to be squarish, it must be a perfect square (since it's odd).

**Case A: $a \leq 5$ (small 2-adic valuation).**

There are only finitely many values of $a$ in $\{0, 1, 2, 3, 4, 5\}$.

For each fixed $a \leq 5$, we show $T_a = \{t \text{ odd} : (2^{a+1} - 1) \cdot \sigma(t^2) \text{ is a square}\}$ is finite.

Fix $a \leq 5$. The number $M = 2^{a+1} - 1$ is a fixed constant.
Write $M = \prod_i q_i^{e_i}$ for its prime factorization.

For $(M) \cdot \sigma(t^2)$ to be a perfect square, for each prime $q_i \mid M$:
$$e_i + v_{q_i}(\sigma(t^2)) \equiv 0 \pmod{2}$$

This places constraints on $t$: for each $q_i$, either $v_{q_i}(\sigma(t^2))$ is even or odd, depending on the parity of $e_i$.

The constraint $v_{q_i}(\sigma(t^2)) \equiv -e_i \pmod{2}$ limits $t$ to a finite set for each $q_i$ because:
- $\sigma(t^2) = \prod_{p \mid t} \sigma(p^{2v_p(t)})$
- For $q_i \mid \sigma(p^{2v})$, we need $q_i \mid (p^{2v+1} - 1)/(p-1)$
- This occurs for finitely many primes $p$ (those with $\mathrm{ord}_{q_i}(p) \mid 2v+1$ or $q_i \mid p-1$)
- The exponent constraint further limits $v_p(t)$

Intersecting the finitely many constraints from all $q_i \mid M$ gives finitely many valid $t$. Hence $T_a$ is finite for each $a \leq 5$.

**Case B: $a \geq 6$ (large 2-adic valuation).**

By Zsygmondy (Lemma 2), for $a \geq 6$, the number $2^{a+1} - 1$ has a primitive prime divisor $p_a$ with $\mathrm{ord}_{p_a}(2) = a + 1 \geq 7$.

For $(2^{a+1} - 1) \cdot \sigma(t^2)$ to be a perfect square, the $p_a$-adic valuation must be even:
$$v_{p_a}(2^{a+1} - 1) + v_{p_a}(\sigma(t^2)) \equiv 0 \pmod{2}$$

**Sub-claim B1:** For any fixed odd $t$, the set $A_t = \{a \geq 6 : (2^{a+1} - 1) \cdot \sigma(t^2) \text{ is a square}\}$ is finite.

*Proof of B1:* Fix $t$ with prime factorization $t = \prod_j r_j^{f_j}$.

For $a \in A_t$, let $p_a$ be a primitive prime divisor of $2^{a+1} - 1$.

For the parity constraint to hold, either:
- $p_a \mid \sigma(t^2)$ with specific parity, or
- $p_a \nmid \sigma(t^2)$ and $v_{p_a}(2^{a+1} - 1)$ is even

Now, $\sigma(t^2) = \prod_j \sigma(r_j^{2f_j}) = \prod_j \frac{r_j^{2f_j+1} - 1}{r_j - 1}$.

For $p_a \mid \sigma(r_j^{2f_j})$, we need:
- $p_a \mid r_j^{2f_j+1} - 1$, i.e., $\mathrm{ord}_{p_a}(r_j) \mid 2f_j + 1$, or
- $p_a \mid r_j - 1$ with appropriate divisibility

Since $\mathrm{ord}_{p_a}(2) = a + 1 \to \infty$ as $a \to \infty$, and the $r_j, f_j$ are fixed, there are only finitely many $a$ for which $p_a$ can divide $\sigma(t^2)$.

More precisely: For each $r_j$, the condition $\mathrm{ord}_{p_a}(r_j) \mid 2f_j + 1$ with $\mathrm{ord}_{p_a}(2) = a+1$ constrains $a$. Since $p_a$ varies with $a$ and $\mathrm{ord}_{p_a}(r_j)$ is bounded by $p_a - 1$ (which grows), eventually $\mathrm{ord}_{p_a}(r_j) > 2f_j + 1$, making $p_a \nmid r_j^{2f_j+1} - 1$.

Once $p_a \nmid \sigma(t^2)$ (which happens for all large enough $a$), the parity constraint becomes $v_{p_a}(2^{a+1} - 1) \equiv 0 \pmod{2}$. This need not hold for all $a$.

Hence $A_t$ is finite for each fixed odd $t$. $\square$

**Sub-claim B2:** For any fixed $a \geq 6$, the set $T_a = \{t \text{ odd} : (2^{a+1} - 1) \cdot \sigma(t^2) \text{ is a square}\}$ is finite.

*Proof of B2:* Fix $a \geq 6$. Let $p = p_a$ be a primitive prime divisor of $M = 2^{a+1} - 1$.

For $t \in T_a$, the constraint $v_p(M) + v_p(\sigma(t^2)) \equiv 0 \pmod 2$ must hold.

The set of odd $t$ with $v_p(\sigma(t^2))$ having a specific parity is finite:

For $v_p(\sigma(t^2)) \geq 1$, we need $p \mid \sigma(r^{2f})$ for some prime power $r^f \| t$. This requires:
- $\mathrm{ord}_p(r) \mid 2f+1$, or
- $p \mid r - 1$ and $p \mid 2f+1$

Since $\mathrm{ord}_p(2) = a + 1 \geq 7$, the prime $p$ is large (at least 7). The primes $r$ with $\mathrm{ord}_p(r)$ dividing small odd numbers form a finite set. The exponents $f$ are also bounded by the constraint.

Hence only finitely many prime powers $r^f$ can contribute $p \mid \sigma(r^{2f})$. The set of $t$ with this property and specific parity of $v_p(\sigma(t^2))$ is finite. $\square$

**Combining Cases A and B:**

In Case A ($a \leq 5$): $T \cap \{2^a \cdot t^2 : t \text{ odd}\} = \{2^a \cdot t^2 : t \in T_a\}$ is finite (union over finitely many $a$).

In Case B ($a \geq 6$): We need to show the union $\bigcup_{a \geq 6} \{2^a \cdot t^2 : t \in T_a\}$ is finite.

By B2, each $T_a$ is finite. By B1, each $t$ belongs to only finitely many $T_a$.

**Claim:** $\bigcup_a T_a$ is finite.

*Proof:* Suppose not. Then there exist infinitely many pairs $(a_j, t_j)$ with $t_j \in T_{a_j}$ and all $(a_j, t_j)$ distinct.

If infinitely many $a_j$ are equal to some fixed $a^*$, then $T_{a^*}$ is infinite, contradicting B2.

So infinitely many distinct values of $a$ appear. By pigeonhole on $t$: either infinitely many distinct $t$ appear, or some $t^*$ appears for infinitely many $a$.

If $t^*$ appears for infinitely many $a$, then $A_{t^*}$ is infinite, contradicting B1.

If infinitely many distinct $t$ appear, consider the finite bound: by B1, each $t$ contributes to only finitely many $a$. If each of the infinitely many $t$ values appears for at least one $a \geq 6$, and if $T_a$ is finite for each $a$, can we still have infinitely many pairs?

Yes, but we can bound: Let $B = \max_{a \leq 100} |T_a|$ (finite). For $t \in T_a$ with $a > 100$, the constraint from B1 bounds $|A_t|$ independently. There exists $C$ such that $|A_t| \leq C$ for all $t$ (by the structure of the constraint). Hence:
$$\sum_{a > 100} |T_a| = \sum_t |A_t \cap \{a : a > 100\}| \leq \sum_t C \cdot \mathbf{1}_{t \in \bigcup_{a > 100} T_a}$$

But this sum is still potentially infinite... Let me reconsider.

**Correct finiteness argument:**

Define $U = \{(a, t) : a \geq 6, t \in T_a\}$. We show $U$ is finite.

Consider the projection maps $\pi_1(a,t) = a$ and $\pi_2(a,t) = t$.

- By B2: Each fiber $\pi_1^{-1}(a) = \{a\} \times T_a$ is finite.
- By B1: Each fiber $\pi_2^{-1}(t) = A_t \times \{t\}$ is finite.

**Key observation:** By B1, for $t$ fixed, $|A_t| \leq C(t)$ where $C(t) \to 0$ as $t \to \infty$ in the following sense: there exists $t_0$ such that for $t > t_0$, we have $A_t = \emptyset$.

This follows because: the constraint $p_a \mid \sigma(t^2)$ for primitive $p_a$ with $\mathrm{ord}_{p_a}(2) = a+1$ requires $a + 1 \leq D(t)$ for some $D(t)$ depending only on $t$. Once $a > D(t)$, the primitive prime $p_a$ is "too large" to divide $\sigma(t^2)$.

More precisely: $\sigma(t^2) \leq \sigma(t)^2 \leq (t \cdot \tau(t))^2$ (very loose bound). So $\sigma(t^2)$ has all prime factors $\leq \sigma(t^2)$.

A primitive prime $p_a$ of $2^{a+1} - 1$ satisfies $p_a > a$ (in fact $p_a \geq a + 1$ since $\mathrm{ord}_{p_a}(2) = a + 1 \leq p_a - 1$).

For $a > \sigma(t^2)$, we have $p_a > \sigma(t^2) \geq$ (any prime factor of $\sigma(t^2)$), so $p_a \nmid \sigma(t^2)$.

Hence $A_t \subseteq \{6, 7, \ldots, \sigma(t^2)\}$ (finite for each $t$), and if $v_{p_a}(2^{a+1}-1)$ is odd for all $a$ in this range with $p_a \nmid \sigma(t^2)$, then $t \notin T_a$.

**Effective bound:** $U \subseteq \{(a, t) : a \leq \max(5, \sigma(t^2))\}$.

For each $t$, only finitely many $a$ work. For each $a$, only finitely many $t$ work (by B2).

The set $T$ is exactly:
$$T = \{1\} \cup \{2^a \cdot t^2 : (a, t) \in U \cup (\{0,\ldots,5\} \times T_0 \cup \cdots \cup T_5)\}$$

This is a finite union of finite sets, hence finite. $\square$

---

## Part 2: Orbit-Specific Finiteness of Squarish Iterates

### Background Facts
From proofs/prime-factors-accumulate.md (Verified ✅):
1. $\sigma_k(n) \to \infty$ as $k \to \infty$
2. $S^* = \bigcup_k \mathrm{primeFactors}(\sigma_k(n))$ is infinite
3. $\omega(\sigma_k(n))$ is unbounded (takes arbitrarily large values)

### Theorem 2 (Eventually Non-Squarish)
For any $n \geq 2$, there exists $K$ such that $\sigma_k(n)$ is not squarish for all $k \geq K$.

**Proof.** The proof proceeds in three stages:

**Stage 1: No consecutive squarish iterates (eventually).**

By Theorem 1, the set $T = \{m : m \text{ squarish}, \sigma(m) \text{ squarish}\}$ is finite.

Let $M_1 = \max T$ (or $M_1 = 1$ if $T = \emptyset$).

Since $\sigma_k(n) \to \infty$, there exists $K_1$ such that $\sigma_k(n) > M_1$ for all $k \geq K_1$.

For $k \geq K_1$: if $\sigma_k(n)$ is squarish, then $\sigma_k(n) > M_1$, so $\sigma_k(n) \notin T$, hence $\sigma_{k+1}(n) = \sigma(\sigma_k(n))$ is NOT squarish.

**Conclusion of Stage 1:** For $k \geq K_1$, consecutive squarish iterates are impossible. The squarish iterates form isolated points in the sequence.

**Stage 2: Characterizing reentry points.**

An index $k \geq K_1$ is a **reentry point** if:
- $\sigma_k(n)$ is NOT squarish
- $\sigma_{k+1}(n)$ IS squarish

By Stage 1, a squarish iterate at $k+1 \geq K_1 + 1$ is always followed by a non-squarish iterate at $k+2$. So squarish iterates occur only at reentry points $+1$.

We must show there are only finitely many reentry points.

At a reentry point $k$: Let $\sigma_k(n) = 2^{a_k} \cdot m_k$ where $m_k$ is odd and NOT a perfect square (since $\sigma_k(n)$ is not squarish).

Then:
$$\sigma_{k+1}(n) = \sigma(2^{a_k}) \cdot \sigma(m_k) = (2^{a_k+1} - 1) \cdot \sigma(m_k)$$

Since $m_k$ is odd and not a square, by Lemma 1, $\sigma(m_k)$ is even.

Write $\sigma(m_k) = 2^{b_k} \cdot Q_k$ where $b_k \geq 1$ and $Q_k$ is odd.

Then:
$$\sigma_{k+1}(n) = (2^{a_k+1} - 1) \cdot 2^{b_k} \cdot Q_k = 2^{b_k} \cdot (2^{a_k+1} - 1) \cdot Q_k$$

For $\sigma_{k+1}(n)$ to be squarish, its odd part must be a perfect square:
$$(2^{a_k+1} - 1) \cdot Q_k \text{ must be a perfect square}$$

**Stage 3: Reentry becomes impossible as prime complexity grows.**

We show that for large enough $k$, the product $(2^{a_k+1} - 1) \cdot Q_k$ cannot be a perfect square.

**Setup:** The odd part of $\sigma_k(n)$ is $m_k$. Since $m_k$ is not a square, there exists an odd prime $p$ with $v_p(m_k)$ odd.

By the Escape Lemma, $\omega(m_k)$ (the number of distinct odd prime factors of $\sigma_k(n)$) is unbounded.

**Key Lemma:** As $\omega(m_k) \to \infty$, the number of "unbalanced" odd prime factors in $(2^{a_k+1} - 1) \cdot Q_k$ also grows, making it impossible for this product to be a perfect square.

*Detailed argument:*

$Q_k$ is the odd part of $\sigma(m_k)$. Since $\sigma$ is multiplicative:
$$\sigma(m_k) = \prod_{p \mid m_k} \sigma(p^{v_p(m_k)})$$

For each odd prime $p \mid m_k$:
- If $v_p(m_k)$ is odd: $\sigma(p^{v_p(m_k)})$ is even, contributing to $b_k$
- If $v_p(m_k)$ is even: $\sigma(p^{v_p(m_k)})$ is odd, contributing directly to $Q_k$

Let $P_{\text{odd}} = \{p \mid m_k : v_p(m_k) \text{ is odd}\}$ (non-empty since $m_k$ is not a square).
Let $P_{\text{even}} = \{p \mid m_k : v_p(m_k) \text{ is even}\}$.

Then:
$$Q_k = \prod_{p \in P_{\text{odd}}} (\text{odd part of } \sigma(p^{v_p(m_k)})) \cdot \prod_{p \in P_{\text{even}}} \sigma(p^{v_p(m_k)})$$

The factors from $P_{\text{odd}}$ are odd parts of $\sigma(p^v)$ for odd $v$. Since $\sigma(p^v) = 1 + p + \cdots + p^v$ and $v$ is odd, this sum has even number of terms, so it's even. The odd part is $(1 + p + \cdots + p^v)/2^{v_2(\sigma(p^v))}$.

**Critical observation:** As new primes enter $m_k$ (via the Escape Lemma), they bring new prime factors into $Q_k$.

Specifically, consider a prime $p$ that first enters the orbit at step $k$ (first divides $\sigma_{k}(n)$ but not earlier). Such primes enter via the formula:
$$p \mid \sigma(q^e) \text{ for some prime power } q^e \| \sigma_{k-1}(n)$$

When $p$ first enters, typically $v_p(\sigma_k(n)) = 1$ (primitive divisors enter with exponent 1).

If $v_p(m_k) = 1$ (odd), then $p \in P_{\text{odd}}$ and contributes to $\sigma(p^1) = p + 1$.

The prime factors of $p + 1$ enter $\sigma(m_k)$ and hence $Q_k$ (after extracting powers of 2).

**Accumulation of constraints:** For $(2^{a_k+1} - 1) \cdot Q_k$ to be a perfect square, every odd prime $r$ in this product must appear to even power.

As $k$ increases:
- New primes enter $m_k$ (Escape Lemma)
- These primes contribute new factors to $Q_k$ via $\sigma(p^{v_p})$
- These new factors must all appear to even power

The constraint becomes increasingly difficult to satisfy because:

1. **Balancing with Mersenne:** The Mersenne number $2^{a_k+1} - 1$ can only "balance" finitely many primes (those dividing it). For $a_k$ in a bounded range, this is a fixed finite set. For $a_k$ large, by Zsygmondy, new primitive primes appear that don't divide $Q_k$ (for $k$ large enough), creating odd exponents.

2. **Balancing within $Q_k$:** For a prime $r \mid Q_k$ to have even exponent, either:
   - $r$ appears from multiple sources that combine to even exponent, or
   - $r$ appears once with even multiplicity from a single $\sigma(p^v)$

   As $\omega(m_k) \to \infty$ and new "fresh" primes enter with exponent 1, the factors $\sigma(p) = p + 1$ introduce new odd primes into $Q_k$ with odd exponent.

**Formal counting argument:**

Let $N_k = |\{r \text{ odd prime} : v_r((2^{a_k+1}-1) \cdot Q_k) \text{ is odd}\}|$.

For the product to be a square, we need $N_k = 0$.

**Claim:** $\limsup_{k \to \infty} N_k = \infty$.

*Proof of Claim:* By the Escape Lemma, $S^* = \bigcup_k \mathrm{primeFactors}(\sigma_k(n))$ is infinite.

Consider primes $p \in S^*$ that are $\equiv 3 \pmod 4$. By Dirichlet's theorem, infinitely many primes are $\equiv 3 \pmod 4$. Since $S^*$ is infinite and contains primes from various residue classes, $S^*$ contains infinitely many primes $\equiv 3 \pmod 4$.

For such a prime $p \equiv 3 \pmod 4$: $p + 1 \equiv 0 \pmod 4$. Write $p + 1 = 4u$ for some $u \geq 1$.

When $p$ enters $m_k$ with odd exponent (e.g., exponent 1), the contribution to $\sigma(m_k)$ includes $\sigma(p) = p + 1 = 4u = 2^2 \cdot u$.

The odd part $u$ contributes to $Q_k$.

If $u$ has an odd prime factor $r$ with $v_r(u) = 1$, then $r \mid Q_k$ with exponent 1, contributing to $N_k$.

As infinitely many such primes $p$ enter the orbit (each bringing at least one factor of $(p+1)/4$ into $Q_k$), and these factors are distinct for distinct $p$ (mostly), $N_k$ grows without bound.

More precisely: the odd primes $r$ arising as factors of $(p+1)/4$ for $p \in S^* \cap \{p \equiv 3 \pmod 4\}$ form a set that grows as $S^*$ grows. Each such $r$ first appears in $Q_k$ for some $k$, and when it first appears, it typically has odd exponent (exponent 1).

For the product $(2^{a_k+1} - 1) \cdot Q_k$ to be a square, all these new primes must be balanced—but the Mersenne number $2^{a_k+1} - 1$ is fixed (for given $k$) and cannot balance infinitely many new primes.

**Conclusion:** For all large enough $k$, $N_k \geq 1$, so $(2^{a_k+1} - 1) \cdot Q_k$ is not a perfect square, hence $\sigma_{k+1}(n)$ is not squarish.

Combined with Stage 1: eventually no $\sigma_k(n)$ is squarish. $\square$

---

## Corollary: 2 Eventually Always Divides

For any $n \geq 2$, there exists $K_2$ such that $2 \mid \sigma_k(n)$ for all $k \geq K_2$.

**Proof.** By Theorem 2, let $K$ be such that $\sigma_k(n)$ is not squarish for all $k \geq K$.

By Corollary 1.1, $\sigma(m)$ is even whenever $m$ is not squarish.

So for $k \geq K$: $\sigma_k(n)$ is not squarish, hence $\sigma_{k+1}(n) = \sigma(\sigma_k(n))$ is even.

Take $K_2 = K + 1$. $\square$

---

## Summary

The proof establishes orbit-specific finiteness of squarish iterates through:

1. **Global structure (Theorem 1):** The transition set $\{m : m, \sigma(m) \text{ both squarish}\}$ is finite, proven via Zsygmondy's theorem on primitive prime divisors of Mersenne numbers.

2. **Dynamical consequence (Stage 1):** Beyond a threshold, consecutive squarish iterates are impossible.

3. **Reentry analysis (Stages 2-3):** For the orbit to re-enter the squarish set, a complex Diophantine condition must hold. As the orbit accumulates more prime factors (Escape Lemma), this condition becomes impossible to satisfy.

The key insight is that while globally there are infinitely many $m$ with $\sigma(m)$ squarish (the Mersenne primes, for instance), the specific constraints of an individual orbit—particularly the unbounded accumulation of prime factors—prevent indefinite reentry.

---

## References

- proofs/prime-factors-accumulate.md (Verified ✅) — Escape Lemma, $\sigma_k(n) \to \infty$, $S^*$ infinite
- Zsygmondy's theorem (1892) for primitive prime divisors of $2^a - 1$
- Dirichlet's theorem on primes in arithmetic progressions

---

## Review Notes

**Reviewer:** Task erdos410-9m4 (verify agent)  
**Date:** 2026-02-08  
**Decision:** Revision Requested 🔍

### Summary

This proof contains a **sound overall strategy** but has **critical gaps** in execution that prevent verification. The orbit-specific approach is correct, and the use of Zsygmondy's theorem is appropriate. However, two key arguments require substantial strengthening:

1. **Part 1 (Transition Set Finite):** The finiteness argument is incomplete
2. **Stage 3 (Reentry Impossible):** The claim that $N_k \to \infty$ is not rigorously proven

### Detailed Issues

#### **Part 1: Transition Set Finiteness**

**Issue 1.1 (Case A, $a \leq 5$):** The claim that $T_a$ is finite for each $a \leq 5$ is asserted without proof. The argument states:

> "This places constraints on $t$: for each $q_i$, either $v_{q_i}(\sigma(t^2))$ is even or odd... Intersecting the finitely many constraints from all $q_i \mid M$ gives finitely many valid $t$."

**Problem:** It is not proven that the parity constraint $v_{q_i}(\sigma(t^2)) \equiv -e_i \pmod 2$ can only be satisfied by finitely many $t$. The assertion "this occurs for finitely many primes $p$" needs justification. Why can't infinitely many $t$ satisfy all the parity constraints simultaneously?

**Issue 1.2 (Case B, Sub-claim B1):** The argument that $A_t = \{a \geq 6 : (2^{a+1} - 1) \cdot \sigma(t^2) \text{ is a square}\}$ is finite for each fixed $t$ is incomplete.

The proof says:
> "Since $\mathrm{ord}_{p_a}(2) = a + 1 \to \infty$ as $a \to \infty$... eventually $\mathrm{ord}_{p_a}(r_j) > 2f_j + 1$"

**Problem:** The relationship between $\mathrm{ord}_{p_a}(2)$ and $\mathrm{ord}_{p_a}(r_j)$ is not established. Why does $p_a$ having large order with respect to 2 imply it has large order with respect to $r_j$? These are independent properties.

The better argument (sketched later) is that $p_a$ is a prime divisor of $2^{a+1} - 1$, and for $a > \sigma(t^2)$, we have $p_a > a > \sigma(t^2)$, so $p_a$ cannot divide $\sigma(t^2)$ (since all primes dividing $\sigma(t^2)$ are $\leq \sigma(t^2)$). But the proof doesn't establish that $p_a > a$ for primitive primes (is this even true?).

**Issue 1.3 (Case B, Combining):** The "König-type" argument to show $\bigcup_{a \geq 6} \{2^a \cdot t^2 : t \in T_a\}$ is finite is **incorrect as stated**.

The proof claims:
> By B2, each $T_a$ is finite. By B1, each $t$ belongs to only finitely many $T_a$. Therefore $\bigcup_a T_a$ is finite.

**Problem:** Having finite fibers under both projections does NOT imply the set is finite. Counterexample: $\{(n, n) : n \in \mathbb{N}\}$ has finite fibers under both coordinate projections but is infinite.

The attempted correction using the bound $A_t \subseteq \{6, 7, \ldots, \sigma(t^2)\}$ is better but still incomplete. It's claimed that this bound is "effective" and makes the set finite, but the actual proof is missing.

**Recommended fix:** Prove directly that $T$ is finite by bounding the elements. For instance, show that for $m = 2^a \cdot t^2 \in T$, both $a$ and $t$ are bounded by an absolute constant (not depending on either variable). The Zsygmondy approach is good for showing constraints, but the finiteness needs a cleaner argument.

#### **Stage 3: Reentry Impossible**

This is the **most critical gap**. The proof needs to show that for large $k$, the quantity $(2^{a_k+1} - 1) \cdot Q_k$ cannot be a perfect square.

**Issue 3.1 (Odd exponents from Escape Lemma):** The proof assumes:

> "When $p$ enters $m_k$ with odd exponent (e.g., exponent 1), the contribution to $\sigma(m_k)$ includes $\sigma(p) = p + 1$."

**Problem:** The Escape Lemma states that new primes enter $\sigma_k(n)$ for some $k$. It does NOT guarantee that:
1. These primes enter $m_k$ (the odd part) rather than just the power of 2
2. These primes enter with exponent 1 (odd) rather than an even exponent

When a new prime $q$ first appears in the orbit, it appears in some $\sigma_k(n)$. If $q = 2$, it doesn't affect $m_k$. If $q$ is odd, it enters $m_k$, but with what exponent? The Escape Lemma says $q \mid \sigma(p_0^a)$ for some $p_0$ already in the orbit. The exponent $v_q(\sigma(p_0^a))$ could be even or odd.

**Issue 3.2 (New odd-exponent primes in $Q_k$):** Even if $p$ enters $m_k$ with odd exponent 1, so $\sigma(p) = p + 1$ divides $\sigma(m_k)$, the proof claims:

> "The prime factors of $p + 1$ enter $\sigma(m_k)$ and hence $Q_k$ (after extracting powers of 2)."

**Problem:** Multiple primes in $m_k$ might contribute the same prime factor $r$ to $Q_k$. For instance, if $p_1, p_2 \in m_k$ (both with odd exponent) and both $r \mid (p_1 + 1)$ and $r \mid (p_2 + 1)$, then $v_r(Q_k)$ gets contributions from both, and the total exponent could be even even if each individual contribution has odd exponent.

The proof acknowledges this with "(mostly)" but doesn't prove that the accumulation of such collisions doesn't eventually balance out to give a perfect square.

**Issue 3.3 (Mersenne factor balancing):** The proof says:

> "The Mersenne number $2^{a_k+1} - 1$ is fixed (for given $k$) and cannot balance infinitely many new primes."

**Problem:** As $k$ varies, $a_k$ varies, so different Mersenne numbers appear. Each Mersenne number $2^{a_k+1} - 1$ has its own factorization, and these could balance different primes at different reentry points. The proof needs to show that across ALL potential reentry points $k \geq K_1$, the accumulation effect dominates, not just that a single Mersenne number can't balance infinitely many primes.

**Issue 3.4 (The divergence claim):** The proof claims:

> "Claim: $\limsup_{k \to \infty} N_k = \infty$"

where $N_k = |\{r \text{ odd prime} : v_r((2^{a_k+1}-1) \cdot Q_k) \text{ is odd}\}|$.

The "proof" argues that primes $p \equiv 3 \pmod 4$ in $S^*$ contribute factors $(p+1)/4$ to $Q_k$, and these accumulate. But this is **informal and incomplete**:

1. Not all reentry indices $k$ will have all these primes in $m_k$ — the orbit is a sequence, not a cumulative set
2. Even if $p \mid m_k$, it might have even exponent, so $\sigma(p^{2j})$ is odd and contributes differently
3. The factors from different primes might combine to give even exponents

**Recommended fix:** A rigorous proof would need to:
- Show that for infinitely many $k$, there exists a prime $p$ with $v_p(m_k)$ odd and $p + 1$ having a prime factor $r$ with $v_r((2^{a_k+1}-1) \cdot Q_k)$ odd
- OR show that the constraints for $(2^{a_k+1}-1) \cdot Q_k$ being a square form a system of Diophantine equations that, combined with the growth properties of the orbit, have only finitely many solutions

An alternative approach: Use the unbounded growth of $\omega(m_k)$ more directly. As $m_k$ has more distinct prime factors with odd exponents, the number of independent parity constraints for $(2^{a_k+1}-1) \cdot Q_k$ being a square grows. With sufficiently many independent constraints, the probability that they all happen to be satisfied becomes vanishingly small (though making this rigorous requires careful analysis).

### What Works Well

1. **Lemma 1 (Parity Criterion):** The characterization of when $\sigma(m)$ is odd is **correct and clearly proven**.

2. **Lemma 2 (Zsygmondy):** Correctly cited and applied.

3. **Stage 1 (No consecutive squarish):** The logic is **sound**: if $T$ is finite (assuming Part 1 is fixed), then eventually all squarish iterates are isolated.

4. **Stage 2 (Reentry characterization):** The setup is **correct**: for a reentry point, $(2^{a_k+1} - 1) \cdot Q_k$ must be a perfect square.

5. **Dependencies:** Correctly references proofs/prime-factors-accumulate.md (Verified ✅). The use of the Escape Lemma and $\omega(m_k)$ unbounded is appropriate.

6. **Overall strategy:** The orbit-specific approach is the right way to proceed (as opposed to global set properties which were proven insufficient).

### Verification Checklist

- ✅ **Statement clarity:** Precise and unambiguous
- ✅ **Assumptions:** Explicitly stated and justified (n ≥ 2, Zsygmondy, Dirichlet)
- ❌ **Logical flow:** Gaps in Part 1 (finiteness) and Stage 3 (divergence)
- ✅ **Quantifiers:** Correctly used in preliminary lemmas
- ⚠️ **Edge cases:** Handled in preliminaries, but not addressed in the main arguments
- ✅ **Dependencies:** Correctly referenced and used appropriately
- ❌ **Completeness:** Does not prove the claimed result rigorously
- ✅ **No circular dependencies:** Dependency chain is clear

### Recommendation

**This proof requires significant revision before it can be verified.** The issues in Part 1 can potentially be addressed by a more direct finiteness argument or by making the Zsygmondy-based approach more rigorous. The issues in Stage 3 are more fundamental and require either:

1. A stronger result from the Escape Lemma about exponents of new primes, OR
2. A different approach to showing reentry is impossible (perhaps probabilistic or density-based), OR
3. A direct construction showing that for large enough $k$, the parity constraints cannot all be satisfied

The current draft represents good mathematical intuition and correct high-level strategy, but the execution has substantial gaps that must be filled before the proof can be considered complete.

### Suggested Next Steps

1. **For Part 1:** Either prove directly that $T$ is finite by bounding its elements, OR fix the Zsygmondy argument by:
   - Proving Case A rigorously for each $a \leq 5$
   - Establishing the bound $p_a > a$ for primitive primes
   - Giving a correct finiteness argument for the union (not the flawed König-type reasoning)

2. **For Stage 3:** Either:
   - Prove a stronger version of the Escape Lemma showing new primes enter with exponent 1, OR
   - Use a counting/density argument to show that the set of $k$ where reentry is possible has density 0, OR  
   - Show directly that the Diophantine constraint $(2^{a_k+1}-1) \cdot Q_k = \text{square}$ combined with $\omega(m_k) \to \infty$ and the specific structure of the orbit implies only finitely many solutions

3. Consider whether a **probabilistic heuristic** could be made rigorous: as $\omega(m_k) \to \infty$, the number of parity constraints grows, and the "probability" that they all align to give a square decreases exponentially, making infinite reentry measure-zero impossible.
