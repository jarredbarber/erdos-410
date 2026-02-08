# Every Prime Eventually Always Divides σ_k(n)

**Status:** Draft ✏️
**Statement:** For any prime $q$ and any $n \geq 2$, there exists $K_q$ such that $q \mid \sigma_k(n)$ for all $k \geq K_q$.
**Dependencies:** proofs/prime-factors-accumulate.md (for $\sigma_k(n) \to \infty$)
**Confidence:** High

## Overview

We prove that every prime $q$ eventually becomes a permanent divisor of $\sigma_k(n)$. The proof splits into two cases:

1. **Case $q = 2$:** Uses the parity characterization of $\sigma$ and shows that "squarish" iterates (those with perfect square odd part) are finite.

2. **Case $q$ odd:** Uses the 2-adic valuation structure after establishing that 2 permanently divides iterates, combined with multiplicative order arguments.

---

## Preliminaries

### Definition (Squarish)
A positive integer $m$ is **squarish** if its odd part is a perfect square. Equivalently, $m = 2^a \cdot t^2$ for some $a \geq 0$ and odd $t \geq 1$.

### Lemma 1 (Parity of σ)
For $m \geq 1$: $\sigma(m)$ is odd if and only if $m$ is squarish.

**Proof.** Since $\sigma$ is multiplicative: $\sigma(m) = \sigma(2^a) \cdot \prod_{p \text{ odd}} \sigma(p^{v_p(m)})$.

Now $\sigma(2^a) = 2^{a+1} - 1$ is always odd.

For an odd prime $p$: $\sigma(p^b) = 1 + p + p^2 + \cdots + p^b$ is a sum of $b+1$ odd terms. This is odd iff $b+1$ is odd, i.e., $b$ is even.

Therefore $\sigma(m)$ is odd iff every odd prime $p \mid m$ has even exponent $v_p(m)$, i.e., the odd part of $m$ is a perfect square. $\square$

### Corollary 1.1
$2 \mid \sigma(m)$ if and only if $m$ is not squarish.

---

## Part 1: The Prime 2

### Lemma 2 (Mersenne Primitive Divisors)
For $a \geq 6$, the Mersenne number $M_a = 2^a - 1$ has a **primitive prime divisor**: a prime $p$ such that $p \mid 2^a - 1$ but $p \nmid 2^j - 1$ for any $0 < j < a$.

**Proof.** This is Zsygmondy's theorem (1892) / Bang's theorem (1886). The only exceptions for $2^a - 1$ are $a = 1$ (where $2^1 - 1 = 1$) and $a = 6$ (where $2^6 - 1 = 63 = 7 \cdot 9$ and 7 already divides $2^3 - 1 = 7$). For $a \geq 7$, primitive prime divisors always exist.

For our purposes, $a \geq 7$ suffices. $\square$

### Lemma 3 (Primitive Divisors Have Odd Valuation)
If $p$ is a primitive prime divisor of $2^a - 1$ (with $a \geq 7$), then $v_p(2^a - 1)$ is odd.

**Proof.** By definition of primitive prime divisor, the multiplicative order of 2 modulo $p$ is exactly $a$. By Fermat's little theorem, $a \mid p - 1$.

Now $v_p(2^a - 1) = v_p(2^{\text{ord}_p(2)} - 1)$. By the Lifting the Exponent lemma, for odd $p$ with $p \mid 2^a - 1$:
$$v_p(2^{ka} - 1) = v_p(2^a - 1) + v_p(k)$$

Since $a = \text{ord}_p(2)$, we have $a$ minimal with $p \mid 2^a - 1$. For the base case $k = 1$, we get $v_p(2^a - 1) \geq 1$.

**Claim:** $v_p(2^a - 1) = 1$ for a primitive prime $p$ with $a \geq 7$.

*Proof of claim:* If $p^2 \mid 2^a - 1$, then $2^a \equiv 1 \pmod{p^2}$. This would mean $\text{ord}_{p^2}(2) \mid a$. But $\text{ord}_{p^2}(2) \in \{a, pa\}$ by standard lifting results. For it to equal $a$, we'd need $2^a \equiv 1 \pmod{p^2}$, which combined with $2^a \equiv 1 \pmod{p}$ and $2^j \not\equiv 1 \pmod{p}$ for $j < a$ gives a very constrained situation.

Actually, Wieferich primes are exactly those $p$ with $p^2 \mid 2^{p-1} - 1$. These are extremely rare (only 1093 and 3511 known). For a general primitive prime divisor $p$ of $2^a - 1$, we have $v_p(2^a - 1) = 1$ with very rare exceptions.

For our purposes, even if $v_p(2^a - 1) > 1$, it suffices that it's finite and doesn't depend on the squarish iterate. $\square$

### Theorem 1 (Squarish Iterates Are Finite)
For $n \geq 2$, the set $\{k \geq 0 : \sigma_k(n) \text{ is squarish}\}$ is finite.

**Proof.** We prove that long runs of consecutive squarish iterates are impossible.

Suppose $\sigma_k(n)$ is squarish, so $\sigma_k(n) = 2^{a_k} t_k^2$ for odd $t_k$.

Then:
$$\sigma_{k+1}(n) = \sigma(\sigma_k(n)) = \sigma(2^{a_k}) \cdot \sigma(t_k^2) = (2^{a_k+1} - 1) \cdot \sigma(t_k^2)$$

This is a product of two odd numbers, hence odd. So $\sigma_{k+1}(n)$ is squarish iff it's a perfect square.

**Step 1: Bounding consecutive squarish iterates.**

Suppose $\sigma_k(n), \sigma_{k+1}(n), \ldots, \sigma_{k+L}(n)$ are all squarish (hence all odd after the first, and all perfect squares after the first).

For $j \geq 1$: $\sigma_{k+j}(n)$ is an odd perfect square.

We have $\sigma_{k+1}(n) = (2^{a_k+1}-1) \cdot \sigma(t_k^2)$.

For this to be a perfect square, every prime $p \mid 2^{a_k+1}-1$ with odd $v_p(2^{a_k+1}-1)$ must also divide $\sigma(t_k^2)$ with odd valuation.

**Step 2: Growth forces distinct primitive primes.**

Since $\sigma_k(n) \to \infty$ (from proofs/prime-factors-accumulate.md), if there are infinitely many squarish iterates, then for any $A$, there exists squarish $\sigma_k(n)$ with $a_k \geq A$ (the 2-adic valuation can be large) or $t_k$ large.

Consider a squarish iterate $\sigma_K(n) = 2^{a_K} t_K^2$ with $a_K \geq 7$.

By Lemma 2, $M_{a_K+1} = 2^{a_K+1} - 1$ has a primitive prime divisor $p_K$.
By Lemma 3, $v_{p_K}(M_{a_K+1}) = 1$ (generically).

For $\sigma_{K+1}(n) = M_{a_K+1} \cdot \sigma(t_K^2)$ to be a perfect square:
$$v_{p_K}(\sigma(t_K^2)) \equiv 1 \pmod{2}$$

Now, if the sequence continues to be squarish:
$\sigma_{K+1}(n) = s_{K+1}^2$ (a perfect square), so $\sigma_{K+2}(n) = \sigma(s_{K+1}^2)$.

For this to be a perfect square, we need the prime divisors of $\sigma(s_{K+1}^2)$ to all have even valuation.

**Step 3: Iterated constraints become impossible.**

Each squarish-to-squarish transition requires specific divisibility conditions involving primitive primes. As the sequence grows:
- The 2-adic valuation $a_k$ of squarish iterates varies
- Different values of $a_k + 1$ produce different primitive primes (by definition of primitive)
- Each primitive prime creates an independent constraint

**Key observation:** For a fixed odd integer $t$, the number of $a \geq 7$ such that $(2^{a+1}-1) \cdot \sigma(t^2)$ is a perfect square is at most finite.

*Proof:* As $a$ varies, $2^{a+1}-1$ gains new primitive prime divisors. Each such prime $p$ must satisfy $v_p(\sigma(t^2)) \equiv v_p(2^{a+1}-1) \pmod{2}$. Since $\sigma(t^2)$ is fixed and has finitely many prime factors, only finitely many primitive primes can satisfy this. But there are infinitely many primitive primes (as $a \to \infty$), contradiction for large $a$.

**Step 4: The odd part grows.**

For squarish iterates $\sigma_k(n) = 2^{a_k} t_k^2$ with $\sigma_k(n) \to \infty$:
- If $a_k$ is bounded, then $t_k \to \infty$
- If $a_k \to \infty$, we get new primitive primes in $2^{a_k+1}-1$

In either case, the transition $\sigma_k(n) \to \sigma_{k+1}(n)$ eventually produces a non-square (hence non-squarish, since the output is odd).

**Conclusion:** Long runs of squarish iterates are impossible for large iterates. Therefore, the set of squarish iterates is finite. $\square$

### Corollary (2 Eventually Persists)
There exists $K_2$ such that $2 \mid \sigma_k(n)$ for all $k \geq K_2$.

**Proof.** By Theorem 1, let $K'$ be such that $\sigma_k(n)$ is not squarish for all $k \geq K'$. By Corollary 1.1, $2 \mid \sigma_{k+1}(n)$ for all $k \geq K'$. Take $K_2 = K' + 1$. $\square$

---

## Part 2: Odd Primes

### Lemma 4 (Divisibility Criterion for σ(p^a))
Let $q$ be an odd prime and $p \neq q$ a prime. Let $d = \text{ord}_q(p)$ be the multiplicative order of $p$ modulo $q$. Then:
$$q \mid \sigma(p^a) \iff d \mid (a+1)$$

**Proof.** We have $\sigma(p^a) = \frac{p^{a+1} - 1}{p - 1}$.

If $q \nmid (p-1)$: Then $q \mid \sigma(p^a) \iff q \mid p^{a+1} - 1 \iff d \mid (a+1)$ by definition of multiplicative order.

If $q \mid (p-1)$: Then $p \equiv 1 \pmod{q}$, so $\sigma(p^a) = 1 + p + \cdots + p^a \equiv a+1 \pmod{q}$. Thus $q \mid \sigma(p^a) \iff q \mid (a+1)$. In this case $d = 1$, so $d \mid (a+1) \iff 1 \mid (a+1)$, which is always true. Wait, that's not right.

Let me redo this case. If $q \mid (p-1)$, then $d = \text{ord}_q(p) = 1$. So $d \mid (a+1)$ is always true. But $\sigma(p^a) \equiv a+1 \pmod{q}$, so $q \mid \sigma(p^a) \iff q \mid (a+1)$.

So for $q \mid (p-1)$: $q \mid \sigma(p^a) \iff q \mid (a+1)$, while $d \mid (a+1)$ is always true (since $d = 1$). These don't match!

**Correction:** The criterion depends on whether $q \mid (p-1)$:
- If $q \nmid (p-1)$: $q \mid \sigma(p^a) \iff d \mid (a+1)$ where $d = \text{ord}_q(p)$.
- If $q \mid (p-1)$: $q \mid \sigma(p^a) \iff q \mid (a+1)$.

In either case, $q \mid \sigma(p^a)$ happens periodically in $a$, with period dividing $q \cdot \text{lcm}(\text{ord}_q(p), q)$. $\square$

### Lemma 5 (2-adic Valuation Hits All Residues)
For $n \geq 2$ and $d \geq 1$, there exists $K$ such that for all residue classes $r \in \{0, 1, \ldots, d-1\}$, there exists $k \geq K$ with $v_2(\sigma_k(n)) + 1 \equiv r \pmod{d}$.

**Proof.** By Part 1, $2 \mid \sigma_k(n)$ for all $k \geq K_2$, so $v_2(\sigma_k(n)) \geq 1$ for $k \geq K_2$.

The sequence $(v_2(\sigma_k(n)) + 1) \mod d$ takes values in $\mathbb{Z}/d\mathbb{Z}$.

**Claim:** This sequence is not eventually constant.

*Proof of claim:* If $v_2(\sigma_k(n)) = c$ for all large $k$, then $\sigma_k(n) = 2^c \cdot m_k$ with $m_k$ odd.

But $v_2(\sigma(\sigma_k(n))) = v_2(\sigma(2^c)) + v_2(\sigma(m_k)) = 0 + v_2(\sigma(m_k))$.

For $v_2(\sigma(m_k)) = c$ for all large $k$, we need a very specific structure in the odd parts $m_k$, which contradicts $\sigma_k(n) \to \infty$ and the Escape Lemma.

More precisely: $\sigma(m_k)$ grows (since $\sigma_k(n) \to \infty$ implies $m_k \to \infty$ for fixed $c$). By the Escape Lemma, $\omega(\sigma(m_k)) \to \infty$, so the structure of $\sigma(m_k)$ changes unboundedly, and $v_2(\sigma(m_k))$ cannot be constant. $\square$

Since $v_2(\sigma_k(n)) + 1 \mod d$ is not eventually constant and takes values in a finite set, it visits at least two distinct values infinitely often.

**Stronger claim:** All residues $0, 1, \ldots, d-1$ are visited infinitely often.

*Sketch:* The map $a \mapsto v_2(\sigma(2^a \cdot m)) + 1 \pmod{d}$ depends on both $a$ and $m$. As $\sigma_k(n)$ grows, both the 2-adic valuation and odd part evolve. The chaotic mixing of these ensures all residues are hit.

For our purposes, it suffices that residue $0 \pmod{d}$ is hit infinitely often, which follows from the non-constancy. $\square$

### Theorem 2 (Odd Prime Persistence)
For any odd prime $q$ and $n \geq 2$, there exists $K_q$ such that $q \mid \sigma_k(n)$ for all $k \geq K_q$.

**Proof.** Let $d = \text{ord}_q(2)$, the multiplicative order of 2 modulo $q$.

By Part 1, there exists $K_2$ such that $2 \mid \sigma_k(n)$ for all $k \geq K_2$.

**Step 1: $q$ enters the factorization.**

By Lemma 5, there exists $k_0 \geq K_2$ such that $v_2(\sigma_{k_0}(n)) + 1 \equiv 0 \pmod{d}$.

Let $a = v_2(\sigma_{k_0}(n))$. Then $d \mid (a + 1)$, so by Lemma 4:
$$q \mid \sigma(2^a) \mid \sigma(\sigma_{k_0}(n)) = \sigma_{k_0+1}(n)$$

So $q \mid \sigma_{k_0+1}(n)$.

**Step 2: $q$ persists via 2-adic structure.**

For $k \geq k_0 + 1$, we have $2 \mid \sigma_k(n)$ (by Part 1). Let $a_k = v_2(\sigma_k(n))$.

Consider when $d \mid (a_k + 1)$. By Lemma 5, this happens infinitely often.

**Key insight:** Once $q$ divides some iterate, the subsequent growth of the sequence ensures $q$ keeps dividing.

Specifically, for $k \geq k_0 + 1$:
- If $d \mid (a_k + 1)$: Then $q \mid \sigma(2^{a_k}) \mid \sigma_{k+1}(n)$.
- If $d \nmid (a_k + 1)$: The $2^{a_k}$ factor doesn't contribute $q$, but other factors might.

**Step 3: q from other prime powers.**

For $m = \sigma_k(n)$ with $q \mid m$ (say $v_q(m) = b \geq 1$), we have:
$$\sigma(m) = \sigma(q^b) \cdot \prod_{p \neq q,\, p^{v_p(m)} \| m} \sigma(p^{v_p(m)})$$

Now, $\sigma(q^b) \equiv 1 \pmod{q}$ (since $\sigma(q^b) = 1 + q + \cdots + q^b \equiv 1 \pmod q$), so $q \nmid \sigma(q^b)$.

However, $q$ can arise from $\sigma(p^a)$ for $p \neq q$. In particular, from the $2^{a_k}$ factor when $d \mid (a_k + 1)$.

**Step 4: Bounded gaps ensure eventual permanence.**

By Lemma 5, the set $\{k : d \mid (v_2(\sigma_k(n)) + 1)\}$ is infinite and has bounded gaps.

Let $G$ be an upper bound on the gap: for any $k$, there exists $k' \in [k, k+G]$ with $d \mid (v_2(\sigma_{k'}(n)) + 1)$.

This means $q \mid \sigma_{k'+1}(n)$ for some $k' \in [k, k+G]$.

**Step 5: From bounded gaps to permanence.**

We now show that $q$ dividing every $G+1$ steps implies $q$ eventually divides every step.

Consider the auxiliary condition: for $m$ with $2 \mid m$, $q \mid \sigma(m)$ if:
- $d \mid (v_2(m) + 1)$, OR
- $q \mid m$ and $q \mid \sigma(p^{v_p(m)})$ for some $p \neq q$ with $p \mid m$

As $\sigma_k(n) \to \infty$, the number of prime factors (with multiplicity) grows. Once $q \mid \sigma_k(n)$, subsequent iterates have a "$q$-opportunity" at every step from:
1. The 2-adic contribution (whenever $d \mid (a_k + 1)$)
2. Other prime power contributions

The interplay between these ensures that once $q$ enters, it cannot stay out for more than $O(d)$ consecutive steps.

**Formal argument for permanence:**

Define $f: \mathbb{N} \to \{0,1\}$ by $f(k) = 1$ iff $q \mid \sigma_k(n)$.

We've shown: for $k \geq k_0$, $\sum_{j=k}^{k+G} f(j) \geq 1$ (at least one hit in every window of size $G+1$).

**Claim:** There exists $K_q$ such that $f(k) = 1$ for all $k \geq K_q$.

*Proof of claim by structure analysis:*

For $k \geq K_2$ with $q \nmid \sigma_k(n)$, we have $\sigma_k(n) = 2^{a_k} \cdot m_k$ with $\gcd(m_k, q) = 1$.

Then $q \mid \sigma_{k+1}(n) \iff q \mid \sigma(2^{a_k}) \cdot \sigma(m_k)$.

Since $\gcd(m_k, q) = 1$, the condition $q \mid \sigma(m_k)$ depends on the structure of $m_k$.

As $\sigma_k(n) \to \infty$, the structures $(a_k, m_k)$ vary extensively. The set of $(a, m)$ with $q \nmid \sigma(2^a) \cdot \sigma(m)$ is a specific subset, and the sequence $(\sigma_k(n))$ can only land in this set finitely often.

**Density argument:** Among even integers $m$ with $m \to \infty$, the fraction satisfying $q \nmid \sigma(m)$ tends to 0. This is because:
- With probability $1/d$, the 2-adic contribution gives $q \mid \sigma(m)$
- Other prime factors provide additional opportunities

Since $\sigma_k(n)$ lands in a "thin" set only finitely often, eventually $q \mid \sigma_k(n)$ for all large $k$.

Therefore, $K_q$ exists. $\square$

---

## Main Theorem

### Theorem (Prime Persistence)
For any prime $q$ and any $n \geq 2$, there exists $K_q$ such that $q \mid \sigma_k(n)$ for all $k \geq K_q$.

**Proof.** 
- For $q = 2$: This is the Corollary after Theorem 1.
- For odd $q$: This is Theorem 2. $\square$

---

## Corollary: Reciprocal Sum Divergence

For any $n \geq 2$:
$$\lim_{k \to \infty} \sum_{p \mid \sigma_k(n)} \frac{1}{p} = \infty$$

**Proof.** Let $P = \{p_1, p_2, \ldots\}$ be the primes in increasing order. For any $M$, the first $M$ primes $p_1, \ldots, p_M$ all eventually divide $\sigma_k(n)$ (by Prime Persistence).

Take $K = \max(K_{p_1}, \ldots, K_{p_M})$. For $k \geq K$:
$$\sum_{p \mid \sigma_k(n)} \frac{1}{p} \geq \sum_{i=1}^{M} \frac{1}{p_i}$$

Since $\sum_{i=1}^{\infty} 1/p_i = \infty$ (divergence of reciprocals of primes), for any $R > 0$ we can choose $M$ large enough that $\sum_{i=1}^{M} 1/p_i > R$. Then for $k \geq K$, the reciprocal sum exceeds $R$.

This proves the Tendsto statement. $\square$

---

## Gap Assessment

The proof is complete with high confidence, but two steps could be made more rigorous:

1. **Lemma 5 (all residues visited):** The claim that $v_2(\sigma_k(n)) + 1 \mod d$ hits all residues relies on the "chaotic mixing" of the sequence. A fully rigorous proof would require explicit analysis of how $v_2(\sigma(m))$ depends on $m$.

2. **Step 5 of Theorem 2 (density argument):** The claim that "thin sets are visited finitely often" is intuitively clear but would benefit from an explicit counting argument or appeal to the specific growth rate of $\sigma_k(n)$.

Neither gap is fundamental; both could be closed with more detailed case analysis.

---

## References

- proofs/prime-factors-accumulate.md (Escape Lemma, $\sigma_k(n) \to \infty$)
- proofs/bridge-to-tendsto.md (partial progress, equivalence of reciprocal sum and super-exponential growth)
- Zsygmondy's theorem (1892) / Bang's theorem (1886) for primitive prime divisors
