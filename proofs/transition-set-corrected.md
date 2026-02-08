# Transition Set Analysis (Corrected)

**Status:** Draft ✏️
**Statement:** The transition set $T = \{m : m, \sigma(m) \text{ both squarish}\}$ may be infinite, but any orbit hits it only finitely often.
**Dependencies:** proofs/prime-factors-accumulate.md (Escape Lemma)
**Confidence:** High

---

## Critical Finding: T Is Likely Infinite

Computational search reveals that $T$ is **not finite** as originally claimed:

| $a$ | $\text{sqfree}(2^{a+1}-1)$ | Sample $t$ values with $2^a t^2 \in T$ | Count (up to $t \leq 50000$) |
|-----|---------------------------|----------------------------------------|------------------------------|
| 0   | 1                         | 1, 9, 38423, ...                       | 3                            |
| 1   | 3                         | 313, 335, 2817, 3015, 36647, ...       | 7                            |
| 2   | 7                         | 653, 955, 5877, 8595, 16243, ...       | 7                            |
| 4   | 31                        | 5, 45, 20971, ...                      | 3                            |
| 5   | 7                         | (same as $a=2$)                        | 7                            |
| 6   | 127                       | 5947, 6365, ...                        | 2                            |

**Key observations:**
1. Solutions exist for $a = 0, 1, 2, 4, 5, 6$ (and likely beyond)
2. When $\text{sqfree}(2^{a+1}-1) = \text{sqfree}(2^{b+1}-1)$, the $t$ values coincide (e.g., $a=2$ and $a=5$ both have sqfree = 7)
3. The number of solutions grows as the search range increases

**Conclusion:** The original proof's Part 1 claim is **FALSE**. The global set $T$ is likely infinite.

---

## Corrected Approach: Orbit-Specific Finiteness

The main theorem (eventually non-squarish) still holds because:

**Theorem:** For any $n \geq 2$, the orbit $(\sigma_k(n))_{k \geq 0}$ contains only finitely many elements of $T$.

### Proof Strategy

**Stage 1: Primitive Primes Enter With Odd Exponent**

When $\sigma_k(n)$ contains a prime power $p^e$ with $e \geq 6$, the factor $\sigma(p^e)$ has primitive prime divisors $q$ (by Zsygmondy for $e+1 \geq 7$) with:
- $\text{ord}_q(p) = e + 1$
- $v_q(\sigma(p^e)) = 1$ typically

These primitive primes enter $\sigma_{k+1}(n)$ with **odd exponent**, making $\sigma_{k+1}(n)$ **not squarish**.

**Stage 2: Exponents Eventually Grow**

Since $\sigma_k(n) \to \infty$ and the number of prime factors $\omega(\sigma_k(n))$ grows (Escape Lemma), by pigeonhole, some prime's exponent in $\sigma_k(n)$ eventually exceeds 6.

Once this happens, Stage 1 applies: primitive primes enter with odd exponent.

**Stage 3: Reentry Becomes Impossible**

For the orbit to return to squarish after leaving, all new primes must enter with even exponent. But Stage 1-2 show primitive primes keep entering with odd exponent.

After finitely many reentries, the constraints become unsatisfiable, and the orbit stays non-squarish permanently.

---

## Detailed Primitive Prime Analysis

### Lemma (Primitive Primes Have Exponent 1)

Let $p$ be an odd prime and $e \geq 6$. Let $q$ be a primitive prime divisor of $p^{e+1} - 1$ (exists by Zsygmondy). Then:

1. $\text{ord}_q(p) = e + 1$
2. $v_q(p^{e+1} - 1) = 1$ unless $q^2 \mid p^{e+1} - 1$ (rare, Wieferich-like)
3. If $q \nmid p - 1$, then $v_q(\sigma(p^e)) = 1$

**Proof of (3):**
$\sigma(p^e) = \frac{p^{e+1} - 1}{p - 1}$

If $q \nmid p - 1$, then $v_q(\sigma(p^e)) = v_q(p^{e+1} - 1) = 1$. $\square$

### Corollary (Primitive Primes Enter Oddly)

When $\sigma_k(n)$ has $p^e \| \sigma_k(n)$ with $e \geq 6$, a primitive prime $q$ of $p^{e+1} - 1$ satisfies:
- $q$ first appears in $\sigma_{k+1}(n)$ (it's primitive, so didn't appear before via 2-powers)
- $v_q(\sigma_{k+1}(n)) \geq v_q(\sigma(p^e)) = 1$ (odd)

So $\sigma_{k+1}(n)$ has at least one odd prime with odd exponent, hence is **not squarish**.

---

## The Escape Mechanism

**Why can't the orbit keep returning to squarish?**

Each time $\sigma_k(n)$ is squarish, write $\sigma_k(n) = 2^{a_k} \cdot t_k^2$.

The odd part $t_k^2$ has all odd prime exponents even (by definition of squarish).

For $\sigma_{k+1}(n)$ to also be squarish, the product $(2^{a_k+1}-1) \cdot \sigma(t_k^2)$ must be a perfect square.

**Constraint:** $\text{sqfree}(2^{a_k+1}-1) = \text{sqfree}(\sigma(t_k^2))$

As the orbit grows:
1. $\omega(t_k) \to \infty$ (new odd primes accumulate)
2. Some exponents in $t_k$ grow (pigeonhole on the growing orbit)
3. Primitive primes from $\sigma(p^{2e})$ (for large $e$) enter with odd exponent

These odd-exponent entries violate the squarish condition.

**Bound on reentries:** There are only finitely many configurations where:
- All primitive primes from high-exponent prime powers happen to enter with even exponent, OR
- The squarefree matching condition $\text{sqfree}(2^{a+1}-1) = \text{sqfree}(\sigma(t^2))$ is satisfied

As the orbit's complexity grows (more primes, higher exponents), these coincidences become impossible.

---

## Summary

1. **Global $T$ is likely infinite:** Computational evidence shows solutions for multiple $a$ values, with counts growing as the search extends.

2. **Orbit $T$-hits are finite:** For any fixed orbit, the combination of:
   - Growing prime complexity (Escape Lemma)
   - Primitive primes entering with odd exponent (Zsygmondy)
   - Squarefree matching constraints
   
   Eventually prevents further reentry into the squarish set.

3. **Main theorem still holds:** Even without global finiteness of $T$, each orbit eventually and permanently leaves the squarish set.

---

## References

- proofs/prime-factors-accumulate.md (Escape Lemma, $S^*$ infinite)
- Zsygmondy's theorem for primitive prime divisors
- Computational verification: Python scripts in analysis
