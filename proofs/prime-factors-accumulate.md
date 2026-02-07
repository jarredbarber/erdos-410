# Prime Factors Accumulate Under Iterated σ

**Status:** Draft ✏️
**Statement:** For all $n \geq 2$, the set $S^* = \bigcup_{k \geq 0} \mathrm{primeFactors}(\sigma_k(n))$ is infinite. In particular, $\omega(\sigma_k(n))$ is unbounded.
**Dependencies:** None (self-contained)
**Confidence:** Certain

## Proof

### Key Lemma (Escape Lemma)

**Lemma.** For any prime $p$ and any finite set $T$ of primes with $p \notin T$, there exists $A$ such that for all $a \geq A$, the quantity $\sigma(p^a) = \frac{p^{a+1} - 1}{p - 1}$ has a prime factor not in $T$.

**Proof.** For each $q \in T$, we bound $v_q(p^{a+1} - 1)$ (the $q$-adic valuation).

Let $d_q = \mathrm{ord}_q(p)$ be the multiplicative order of $p$ modulo $q$. If $d_q \nmid (a+1)$, then $q \nmid p^{a+1} - 1$, so $v_q(p^{a+1}-1) = 0$.

If $d_q \mid (a+1)$, write $a+1 = d_q \cdot m$. Then $p^{a+1} - 1 = (p^{d_q})^m - 1^m$.

By the **Lifting the Exponent Lemma** (available in Mathlib as `Nat.emultiplicity_pow_sub_pow` for odd $q$ with $q \mid p^{d_q} - 1$ and $q \nmid p^{d_q}$):

$$v_q(p^{a+1} - 1) = v_q(p^{d_q} - 1) + v_q(m) \leq v_q(p^{d_q} - 1) + \log_q(m)$$

Define $C_q = v_q(p^{d_q} - 1)$, a constant depending only on $p$ and $q$. Then:

$$v_q(p^{a+1} - 1) \leq C_q + \log_q(a+1)$$

(For $q = 2$ and $p$ odd, a similar bound holds using the LTE for $p = 2$; the key point is that $v_2(p^{a+1}-1)$ grows at most logarithmically in $a$.)

Now suppose for contradiction that $\sigma(p^a)$ is $T$-smooth for all $a$. Since $\sigma(p^a) \equiv 1 \pmod{p}$ (the sum $1 + p + \cdots + p^a \equiv 1 \pmod{p}$), we have $p \nmid \sigma(p^a)$. So all prime factors of $\sigma(p^a)$ lie in $T$, hence all prime factors of $p^{a+1} - 1 = (p-1) \cdot \sigma(p^a)$ lie in $T \cup \mathrm{primeFactors}(p-1)$, a finite set $T'$.

Then:
$$p^{a+1} - 1 = \prod_{q \in T'} q^{v_q(p^{a+1}-1)} \leq \prod_{q \in T'} q^{C_q + \log_q(a+1)} = C \cdot (a+1)^{|T'|}$$

where $C = \prod_{q \in T'} q^{C_q}$ is a constant.

But $p^{a+1} - 1$ grows exponentially while $C \cdot (a+1)^{|T'|}$ grows polynomially. For $a$ sufficiently large, $p^{a+1} - 1 > C \cdot (a+1)^{|T'|}$. **Contradiction.** $\square$

### Main Result

**Theorem.** For $n \geq 2$, the set $S^* = \bigcup_{k \geq 0} \mathrm{primeFactors}(\sigma_k(n))$ is infinite.

**Proof.** Suppose for contradiction that $S^*$ is finite.

**Step 1.** We know $\sigma_k(n) \to \infty$ (already proven as `sigma_iterate_tendsto_atTop`). All $\sigma_k(n)$ are $S^*$-smooth (their prime factors all lie in $S^*$).

**Step 2.** Since $\sigma_k(n) \to \infty$ and $\sigma_k(n)$ is $S^*$-smooth with $|S^*| < \infty$, some prime's exponent must grow without bound. Formally: $\sigma_k(n) \leq \prod_{p \in S^*} p^{v_p(\sigma_k(n))} \leq (\max S^*)^{|S^*| \cdot \max_p v_p(\sigma_k(n))}$. Since $\sigma_k(n) \to \infty$, we need $\max_p v_p(\sigma_k(n)) \to \infty$.

By pigeonhole on $S^*$ (which is finite), there exists $p_0 \in S^*$ and a subsequence $k_j$ with $v_{p_0}(\sigma_{k_j}(n)) \to \infty$.

**Step 3.** Since $\sigma$ is multiplicative, $\sigma(\sigma_{k_j}(n)) = \prod_{p \in S_{k_j}} \sigma(p^{v_p(\sigma_{k_j}(n))})$ where $S_{k_j} = \mathrm{primeFactors}(\sigma_{k_j}(n)) \subseteq S^*$.

In particular, $\sigma(p_0^{v_{p_0}(\sigma_{k_j}(n))})$ divides $\sigma(\sigma_{k_j}(n)) = \sigma_{k_j+1}(n)$.

**Step 4.** Apply the Escape Lemma with $p = p_0$ and $T = S^* \setminus \{p_0\}$. There exists $A$ such that for $a \geq A$, $\sigma(p_0^a)$ has a prime factor outside $T$.

Note that $p_0 \nmid \sigma(p_0^a)$ (since $\sigma(p_0^a) \equiv 1 \pmod{p_0}$). So the prime factor outside $T$ is also not $p_0$, hence not in $S^*$.

**Step 5.** For $j$ large enough that $v_{p_0}(\sigma_{k_j}(n)) \geq A$, the number $\sigma(p_0^{v_{p_0}(\sigma_{k_j}(n))})$ has a prime factor $q \notin S^*$. Since $\sigma(p_0^{v_{p_0}(\sigma_{k_j}(n))})$ divides $\sigma_{k_j+1}(n)$, we have $q \mid \sigma_{k_j+1}(n)$, so $q \in \mathrm{primeFactors}(\sigma_{k_j+1}(n)) \subseteq S^*$.

**Contradiction.** Therefore $S^*$ is infinite. $\square$

### Corollary

$\omega(\sigma_k(n))$ is unbounded: for any $M$, there exists $k$ with $\omega(\sigma_k(n)) > M$.

*Proof:* If $\omega(\sigma_k(n)) \leq M$ for all $k$, then $|S^*| \leq M$, contradicting $S^*$ being infinite.

## Gap: From Unbounded to Tendsto

The Lean formalization currently requires the stronger statement `Tendsto (fun k => omega(σ_k(n))) atTop atTop`, meaning for any $M$, EVENTUALLY $\omega(\sigma_k(n)) \geq M$ for all sufficiently large $k$. The above proof only gives "unbounded" (for any $M$, $\omega \geq M$ for SOME $k$).

**Possible approaches to bridge the gap:**

1. **Direct restructuring:** Replace `abundancy_ratio_diverges` (Tendsto of the ratio) with a direct proof of `erdos_410` using the "unbounded ω" result plus Cesaro-type averaging.

2. **Strengthening the induction:** Show that once ω reaches level M, it can only drop below M finitely many times (because the sequence grows, so exponents grow, so the Escape Lemma triggers faster each time).

3. **Alternative formulation:** Prove $\log(\sigma_k(n))/k \to \infty$ directly using the fact that "big ratio" steps occur with sufficient frequency.

## References

- Mathlib's `Nat.emultiplicity_pow_sub_pow` (Lifting the Exponent Lemma)
- Already proven in Lean: `sigma_iterate_tendsto_atTop`, `abundancy_prime_factor_bound`, `prod_one_plus_inv_primes_unbounded`
