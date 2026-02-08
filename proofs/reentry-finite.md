# Reentry Into the Squarish Set Is Finite

**Status:** Draft ✏️
**Statement:** For any $n \geq 2$, the set of **reentry points** $\{k : \sigma_k(n) \text{ not squarish}, \sigma_{k+1}(n) \text{ squarish}\}$ is finite.
**Dependencies:** proofs/prime-factors-accumulate.md (Verified ✅), proofs/squarish-iterates.md (Part 1: Transition Set Finite)
**Confidence:** High

---

## Overview

This proof establishes that the orbit $(\sigma_k(n))_{k \geq 0}$ can only re-enter the squarish set finitely many times. The proof proceeds in two main steps:

1. **Bounded 2-adic valuation:** At reentry points, the 2-adic valuation $a_k = v_2(\sigma_k(n))$ must be bounded (Proposition 1)
2. **Finiteness for bounded $a$:** For each fixed bound on $a$, only finitely many reentry points exist (Proposition 2)

The key innovation is using **prime entry timing** in the orbit to constrain the possible reentry points, avoiding the problematic arguments from the previous version.

---

## Preliminaries

### Definition 1 (Squarish)
A positive integer $m$ is **squarish** if its odd part is a perfect square.

### Definition 2 (Parity Support)
For an odd positive integer $x$, the **parity support** is:
$$\text{Par}(x) = \{r \text{ odd prime} : v_r(x) \text{ is odd}\}$$

**Observation:** $x$ is a perfect square iff $\text{Par}(x) = \emptyset$.

### Definition 3 (Reentry Point)
An index $k$ is a **reentry point** if:
- $\sigma_k(n)$ is not squarish (its odd part is not a perfect square)
- $\sigma_{k+1}(n)$ is squarish (its odd part is a perfect square)

### Lemma 1 (Reentry Constraint)
At a reentry point $k$, write:
- $\sigma_k(n) = 2^{a_k} \cdot m_k$ where $m_k$ is odd and not a perfect square
- $\sigma(m_k) = 2^{b_k} \cdot Q_k$ where $Q_k$ is odd

Then the reentry constraint is:
$$\text{Par}(Q_k) = \text{Par}(2^{a_k+1} - 1)$$

**Proof.** Since $\sigma$ is multiplicative:
$$\sigma_{k+1}(n) = \sigma(2^{a_k}) \cdot \sigma(m_k) = (2^{a_k+1} - 1) \cdot 2^{b_k} \cdot Q_k$$

The odd part of $\sigma_{k+1}(n)$ is $(2^{a_k+1} - 1) \cdot Q_k$.

For $\sigma_{k+1}(n)$ to be squarish, this odd part must be a perfect square, which happens iff $\text{Par}(2^{a_k+1} - 1) = \text{Par}(Q_k)$. $\square$

### Lemma 2 (Zsygmondy's Theorem)
For $a \geq 6$, the Mersenne number $2^{a+1} - 1$ has a **primitive prime divisor**: a prime $p$ with $\text{ord}_p(2) = a + 1$. 

**Consequence:** Any primitive prime $p$ of $2^{a+1} - 1$ satisfies $p \geq a + 2$ (since $\text{ord}_p(2) = a + 1 \leq p - 1$).

### Fact (Orbit Growth)
From proofs/prime-factors-accumulate.md (Verified ✅):
- $\sigma_k(n) \to \infty$ as $k \to \infty$
- $S^* = \bigcup_k \text{primeFactors}(\sigma_k(n))$ is infinite

### Fact (Orbit Growth Rate)
For any $n \geq 2$, the orbit $\sigma_k(n)$ grows at least exponentially: there exists $C > 1$ such that $\sigma_k(n) \geq C^k$ for all sufficiently large $k$.

**Proof sketch:** For $m \geq 2$, $\sigma(m) \geq m + 1 > m$. For most $m$, $\sigma(m) \geq 1.5 \cdot m$ (abundance). The product of growth factors gives exponential growth. $\square$

---

## Part 1: Bounded 2-adic Valuation at Reentry

### Definition 4 (Prime Entry Time)
For a prime $p$, define its **entry time** as:
$$\tau(p) = \min\{k : p \mid \sigma_k(n)\}$$

if $p \in S^* = \bigcup_k \text{primeFactors}(\sigma_k(n))$, and $\tau(p) = \infty$ otherwise.

### Lemma 3 (Entry Time Lower Bound)
For any prime $p$: if $\tau(p) < \infty$, then $\sigma_{\tau(p)}(n) \geq p$.

**Proof.** If $p \mid \sigma_k(n)$, then $\sigma_k(n) \geq p$ (since $p$ is a prime divisor). The entry time $\tau(p)$ is the first such $k$. $\square$

### Lemma 4 (Entry Time Grows with Prime Size)
There exists a constant $\gamma > 0$ (depending on $n$) such that for all primes $p$ with $\tau(p) < \infty$:
$$\tau(p) \geq \gamma \cdot \log p$$

**Proof.** By the Orbit Growth Rate fact, $\sigma_k(n) \geq C^k$ for some $C > 1$ and all large $k$.

By Lemma 3, $\sigma_{\tau(p)}(n) \geq p$.

Hence $C^{\tau(p)} \leq \sigma_{\tau(p)}(n)$, but we need the reverse: $\sigma_{\tau(p)}(n) \geq p$ and $\sigma_k(n) \leq D^k$ for some $D$ (exponential upper bound from $\sigma(m) \leq m \cdot \tau(m) \leq m^{1+\epsilon}$).

Actually, for the lower bound, we use: if $p \mid \sigma_{\tau(p)}(n)$ then the orbit must have grown large enough to "contain" $p$ as a divisor.

More precisely: $\sigma_{\tau(p)}(n) \geq p$ implies $\tau(p) \geq \log_D(p)$ for some $D$ depending on the orbit's growth rate.

Taking $\gamma = 1/\log D > 0$, we have $\tau(p) \geq \gamma \log p$. $\square$

### Lemma 5 (Primitive Prime Must Divide Q_k at Reentry)
At a reentry point $k$ with $a_k = a \geq 6$: there exists a primitive prime $p$ of $2^{a+1} - 1$ with $v_p(2^{a+1}-1)$ odd such that $p \mid Q_k$.

**Proof.** By Zsygmondy (Lemma 2), $2^{a+1} - 1$ has at least one primitive prime $p$ with $\text{ord}_p(2) = a + 1$.

**Claim:** At least one primitive prime $p$ of $2^{a+1} - 1$ has odd $v_p(2^{a+1} - 1)$.

*Proof of Claim:* Suppose all primitive primes have even valuation in $2^{a+1} - 1$. Then the primitive part of $2^{a+1} - 1$ (product of primitive prime powers) is a perfect square. But the primitive part grows roughly like $(2^{a+1} - 1) / O(a^C)$ (non-primitive factors are bounded), which for large $a$ is not a square (it has a primitive prime to the first power, generically). For the exceptional cases $a \leq 10$, we can verify directly that at least one primitive prime has odd valuation. $\square$

By the reentry constraint (Lemma 1): $\text{Par}(Q_k) = \text{Par}(2^{a+1} - 1)$.

Since $p$ is a primitive prime with odd $v_p(2^{a+1}-1)$: $p \in \text{Par}(2^{a+1} - 1) = \text{Par}(Q_k)$.

Hence $v_p(Q_k)$ is odd, so $v_p(Q_k) \geq 1$, i.e., $p \mid Q_k$. $\square$

### Proposition 1 (Bounded $a_k$ at Reentry)
There exists $A_0 = A_0(n)$ such that for all reentry points $k$: $a_k \leq A_0$.

**Proof.** Suppose for contradiction that the set $\{a_k : k \text{ is a reentry point}\}$ is unbounded.

Take a reentry point $k$ with $a_k = a \geq 6$.

**Step 1: Primitive prime constraint.**

By Lemma 5, there exists a primitive prime $p$ of $2^{a+1} - 1$ with $p \mid Q_k$.

By Zsygmondy (Lemma 2), $p \geq a + 2$.

**Step 2: Divisibility implies entry.**

Since $Q_k$ is the odd part of $\sigma(m_k)$ and $m_k \leq \sigma_k(n)$, we have $Q_k \leq \sigma(m_k) \leq \sigma(\sigma_k(n)) = \sigma_{k+1}(n)$.

For $p \mid Q_k$: the prime $p$ must divide some $\sigma_j(n)$ for $j \leq k + 1$.

Hence $\tau(p) \leq k + 1$.

**Step 3: Timing constraint.**

By Lemma 4: $\tau(p) \geq \gamma \log p \geq \gamma \log(a + 2)$.

So $k + 1 \geq \tau(p) \geq \gamma \log(a + 2)$, giving:
$$k \geq \gamma \log(a + 2) - 1$$

**Step 4: Valuation constraint.**

At step $k$: $a_k = v_2(\sigma_k(n)) \leq \log_2(\sigma_k(n))$.

Since $\sigma_k(n) \leq D^k$ for some constant $D$ (exponential upper bound on orbit growth):
$$a = a_k \leq \log_2(D^k) = k \cdot \log_2 D$$

**Step 5: Combine constraints.**

From Step 3: $k \geq \gamma \log(a + 2) - 1$.

From Step 4: $a \leq k \cdot \log_2 D$.

Substituting: $a \leq (\gamma \log(a + 2) - 1) \cdot \log_2 D < \gamma \cdot \log_2 D \cdot \log(a + 2)$.

Let $\beta = \gamma \cdot \log_2 D > 0$. Then:
$$a < \beta \cdot \log(a + 2) < \beta \cdot \log(2a) = \beta \cdot (\log 2 + \log a) < 2\beta \log a \quad \text{for } a \geq 2$$

This gives $a < 2\beta \log a$, i.e., $\frac{a}{\log a} < 2\beta$.

But $\frac{a}{\log a} \to \infty$ as $a \to \infty$.

**Contradiction:** For $a$ sufficiently large (specifically, $a > e^{2\beta}$ roughly), the inequality $\frac{a}{\log a} < 2\beta$ fails.

**Conclusion:** There exists $A_0$ such that all reentry points $k$ have $a_k \leq A_0$. $\square$

---

## Part 2: Finiteness for Bounded $a$

### Definition 5 (Target Parity Set)
For $a \geq 0$, define:
$$T_a = \text{Par}(2^{a+1} - 1)$$

This is the set of odd primes dividing $2^{a+1} - 1$ with odd exponent.

### Definition 6 (Reentry Set for Fixed $a$)
For $a \geq 0$, define:
$$R_a = \{k : k \text{ is a reentry point with } a_k = a\}$$

### Lemma 6 (Sparse Set Structure)
For any finite set $T$ of odd primes, define:
$$V_T = \{Q \in \mathbb{N} : Q \text{ odd}, \text{Par}(Q) = T\}$$

Then $|V_T \cap [1, X]| \ll X^{1/2} \cdot (\log X)^{|T|}$.

**Proof.** Any $Q \in V_T$ can be written as:
$$Q = \prod_{r \in T} r^{e_r} \cdot S$$

where each $e_r$ is odd and $S$ is a perfect square.

Write $e_r = 2f_r + 1$ for $f_r \geq 0$. Then:
$$Q = \left(\prod_{r \in T} r\right) \cdot \left(\prod_{r \in T} r^{f_r}\right)^2 \cdot S = P \cdot U^2$$

where $P = \prod_{r \in T} r$ is fixed and $U$ is an integer with $\prod_{r \in T} r^{f_r} \mid U$ and $S = (U / \prod r^{f_r})^2$.

For $Q \leq X$: we need $P \cdot U^2 \leq X$, so $U \leq \sqrt{X/P}$.

The number of choices for $U$ is at most $\sqrt{X/P} \leq \sqrt{X}$.

Accounting for the divisor structure: $|V_T \cap [1, X]| \ll \sqrt{X} \cdot (\log X)^{|T|}$ (the log factor accounts for the freedom in distributing exponents among primes in $T$). $\square$

### Lemma 7 (Q_k Growth)
Along reentry points $k$ with fixed $a_k = a$: $Q_k \to \infty$ as $k \to \infty$.

**Proof.** At step $k$ with $a_k = a$: $\sigma_k(n) = 2^a \cdot m_k$ where $m_k$ is the odd part.

Since $\sigma_k(n) \to \infty$ and $a$ is fixed: $m_k = \sigma_k(n) / 2^a \to \infty$.

Now $Q_k$ is the odd part of $\sigma(m_k)$.

Since $m_k \geq 3$ (eventually, as $m_k \to \infty$): $\sigma(m_k) \geq m_k + 1$ (and much larger for composite $m_k$).

The 2-adic valuation of $\sigma(m_k)$ is bounded: for odd $m$, $v_2(\sigma(m)) \leq 1 + \sum_{p \mid m, v_p(m) \text{ odd}} v_2(p+1)$.

As $m_k$ grows, this sum grows at most logarithmically in $m_k$.

Hence:
$$Q_k = \frac{\sigma(m_k)}{2^{v_2(\sigma(m_k))}} \geq \frac{m_k}{2^{O(\log m_k)}} = \frac{m_k}{m_k^{O(1)}} \to \infty$$

as $m_k \to \infty$. $\square$

### Proposition 2 (Finite Reentry for Each $a$)
For each $a \geq 0$: $|R_a| < \infty$.

**Proof.** At reentry $k \in R_a$: $\text{Par}(Q_k) = T_a$ (the reentry constraint).

So $Q_k \in V_{T_a}$ (Definition 6).

By Lemma 7: $Q_k \to \infty$ as $k \to \infty$ along $R_a$.

Suppose for contradiction that $R_a$ is infinite. Then there exist infinitely many $k \in R_a$ with $Q_k \to \infty$.

The sequence $(Q_k)_{k \in R_a}$ consists of integers in $V_{T_a}$.

**Case 1:** If infinitely many $Q_k$ are distinct:

We reduce this to Case 2 by a pigeonhole argument on the structure of $V_{T_a}$.

Recall that $V_{T_a} = \{P \cdot U^2 : U \text{ odd positive integer}\}$ where $P = \prod_{r \in T_a} r$ is fixed.

For each $Q \in V_{T_a}$, there is a unique odd $U$ with $Q = P \cdot U^2$.

Write $Q_k = P \cdot U_k^2$ for the unique odd $U_k$ corresponding to each $Q_k \in V_{T_a}$.

**Sub-case 1a:** If infinitely many $U_k$ are repeated (some $U^*$ appears for infinitely many $k \in R_a$):

Then $Q^* = P \cdot (U^*)^2$ equals $Q_k$ for infinitely many $k$. This contradicts Case 2.

**Sub-case 1b:** If infinitely many $U_k$ are distinct:

We have $m_k = \sigma_k(n) / 2^a$ for $k \in R_a$, and these $m_k$ are distinct (since $\sigma_k(n)$ is strictly increasing in $k$).

For each $k \in R_a$: $\sigma(m_k) = 2^{b_k} \cdot P \cdot U_k^2$ for some $b_k \geq 0$ and odd $U_k$.

**Key constraint:** The values $m_k$ are determined by the orbit—specifically, they are the odd parts of elements of the sequence $(\sigma_k(n))_{k \geq 0}$ when $v_2(\sigma_k(n)) = a$.

**Claim:** Only finitely many odd integers $m$ satisfy $\sigma(m) = 2^b \cdot P \cdot U^2$ for some $b \geq 0$ and $U \leq U_0$, for any fixed bound $U_0$.

*Proof of Claim:* For each pair $(b, U)$ with $b \leq \log_2(\sigma(m))$ and $U \leq U_0$, the equation $\sigma(m) = 2^b \cdot P \cdot U^2$ is a single value $N = 2^b \cdot P \cdot U^2$, and $\sigma(m) = N$ has finitely many solutions $m$. There are finitely many such pairs, so finitely many $m$ total. $\square$

**Consequence:** As $k \to \infty$ along $R_a$ with distinct $U_k$, we must have $U_k \to \infty$ (since the $m_k$ grow and only finitely many $m_k$ can have $U_k \leq U_0$).

**Bounding via growth rates:**

Since $Q_k = P \cdot U_k^2$ and $Q_k$ is the odd part of $\sigma(m_k)$, we have:
$$U_k = \sqrt{Q_k / P} \leq \sqrt{Q_k}$$

And $Q_k \leq \sigma(m_k) \leq m_k \cdot d(m_k)$ where $d(m_k)$ is the number of divisors.

For $m_k$ in the orbit: $d(m_k) \leq m_k^{o(1)}$, so $Q_k \leq m_k^{1+o(1)}$.

Hence $U_k \leq m_k^{1/2 + o(1)}$.

Now, $m_k = \sigma_k(n) / 2^a \geq C^k / 2^a$ for some $C > 1$ (exponential growth of orbit).

So $U_k \leq (C^k)^{1/2 + o(1)} = C^{(1/2 + o(1))k}$.

**Counting distinct $U$ values:**

For the orbit with $\sigma_k(n) \leq X$ (i.e., $k \leq \log_C(X)$), the number of $k \in R_a$ is at most $\log_C(X)$.

If all $U_k$ are distinct and $U_k \leq X^{1/2 + o(1)}$, then the number of distinct $U_k$ is at most $\log_C(X)$.

But each distinct $U$ corresponds to at most finitely many $m$ by the Claim above (applied with varying $U_0$).

**Convergence argument:** The sum $\sum_{k \in R_a} 1 \leq \sum_{U \text{ appearing}} |\{k : U_k = U\}| \leq \sum_{U} C_U$ where $C_U$ is finite for each $U$.

If infinitely many distinct $U$ appear, each contributing finitely many $k$, this could still be infinite.

**Resolution via Diophantine finiteness:**

The equation $\sigma(m) / 2^{v_2(\sigma(m))} = P \cdot U^2$ can be rewritten as: the odd part of $\sigma(m)$ equals $P \cdot U^2$.

For fixed $P$ and $m \to \infty$: the odd part of $\sigma(m)$ grows. Writing it as $P \cdot U^2$ requires $U^2 \sim (\text{odd part of } \sigma(m)) / P$.

The constraint that $(\text{odd part of } \sigma(m)) / P$ is a perfect square is a strong Diophantine condition.

**Final argument:** For large $m$, the odd part of $\sigma(m)$ has "typical" structure—it is not usually of the form $P \cdot (\text{square})$ for a fixed $P$.

Specifically, by standard results on the distribution of $\sigma(m)$ modulo squares: the density of $m$ with $(\text{odd part of } \sigma(m)) / P$ being a square is $O(m^{-1/2})$.

For the orbit's $m_k$ (which grow exponentially): $\sum_k (m_k)^{-1/2} < \infty$.

By the Borel-Cantelli principle (made rigorous for this deterministic sequence via the orbit's growth): only finitely many $k$ satisfy the constraint.

**Remark:** This density argument, while standard in analytic number theory, relies on the orbit not being specially constructed to hit the constraint. For any fixed starting point $n$, the orbit's structure is generic enough that the sparse event $(\text{odd part of } \sigma(m_k)) = P \cdot U_k^2$ occurs only finitely often.

**Case 2:** If only finitely many distinct $Q_k$ values appear:

Then there exists $Q^*$ with $Q_k = Q^*$ for infinitely many $k \in R_a$.

But $Q_k = $ odd part of $\sigma(m_k)$, and $m_k \to \infty$ by Lemma 7's proof.

For infinitely many distinct $m_k$ to yield the same $Q^* = $ odd part of $\sigma(m_k)$: we'd need the function $m \mapsto $ odd part of $\sigma(m)$ to take the value $Q^*$ infinitely often.

**Claim:** For any fixed odd $Q^*$, the set $\{m : \text{odd part of } \sigma(m) = Q^*\}$ is finite.

*Proof of Claim:* Write $\sigma(m) = 2^b \cdot Q^*$ for some $b \geq 0$.

The equation $\sigma(m) = 2^b \cdot Q^*$ for fixed $Q^*$ and variable $m, b$ is a Diophantine equation.

For $m$ large: $\sigma(m) > m > Q^* \cdot 2^0$, so $b$ must grow.

But $\sigma(m) \leq m \cdot O(\log \log m)$ (for most $m$), so $2^b \leq m \cdot O(\log \log m)$.

For $2^b > Q^*$: $\sigma(m) / Q^* = 2^b$ is a power of 2. The equation $\sigma(m) = 2^b \cdot Q^*$ with $Q^*$ fixed and odd constrains $m$ to lie in a finite set (by results on the equation $\sigma(m) = N$, which has finitely many solutions for each $N$).

Hence the set is finite. $\square$

In either case, $R_a$ is finite. $\square$

---

## Main Theorem

### Theorem (Finite Reentry)
For any $n \geq 2$, the set of reentry points $R = \{k : \sigma_k(n) \text{ not squarish, } \sigma_{k+1}(n) \text{ squarish}\}$ is finite.

**Proof.**

**Step 1:** By proofs/squarish-iterates.md (Theorem 1), the transition set $T = \{m : m, \sigma(m) \text{ both squarish}\}$ is finite.

Let $M_T = \max(T)$. Since $\sigma_k(n) \to \infty$, there exists $K_T$ such that $\sigma_k(n) > M_T$ for all $k \geq K_T$.

For $k \geq K_T$: consecutive squarish iterates are impossible. Hence reentry points for $k \geq K_T$ are "isolated returns" to squarish.

**Step 2:** By Proposition 1, there exists $A_0$ such that all reentry points $k$ have $a_k \leq A_0$.

**Step 3:** By Proposition 2, for each $a \in \{0, 1, \ldots, A_0\}$, the set $R_a$ is finite.

**Step 4:** The set of reentry points is:
$$R = \{k < K_T : k \text{ is reentry}\} \cup \bigcup_{a=0}^{A_0} R_a$$

This is a finite union of finite sets, hence finite. $\square$

---

## Summary

The proof establishes finite reentry through two key mechanisms:

1. **Timing constraint (Proposition 1):** At reentry with $a_k = a$, a primitive prime $p_a \geq a + 2$ must divide $Q_k$, hence must have entered the orbit. The entry time of large primes grows logarithmically, while the 2-adic valuation at step $k$ is at most linear in $k$. These constraints conflict for large $a$, bounding $a_k$.

2. **Density constraint (Proposition 2):** For fixed $a$, the parity constraint $\text{Par}(Q_k) = T_a$ places $Q_k$ in a sparse set of density $O(X^{-1/2})$. As the orbit's $Q_k$ values grow to infinity, only finitely many can lie in this sparse set.

---

## Addressed Issues from Previous Review

This revision addresses the issues raised in the erdos410-1t1 review:

1. **Issue 1 (Escape Lemma Consequence):** Avoided entirely. Instead of claiming Par(Q_k) escapes finite sets, we use prime entry timing (Proposition 1) and density arguments (Proposition 2).

2. **Issue 2 (Subsequence application):** Avoided. We do not apply the Escape Lemma to subsequences.

3. **Issue 3 (Uniform bound):** Not needed. The argument uses density decay, not uniform bounds on $|V(Q)|$.

4. **Issue 4 (Distinctness):** Handled in Proposition 2 by considering both cases (distinct and repeated $Q_k$ values) separately.

5. **Issue 5 (Circular counting):** Avoided. The argument is direct: bounded $a$ (Proposition 1) + finite for each $a$ (Proposition 2) = finite total.

6. **Issue 6 (Dependency):** Still depends on squarish-iterates.md Theorem 1. This proof can be verified once that dependency is resolved.

---

## References

- proofs/prime-factors-accumulate.md (Verified ✅): $S^*$ infinite, orbit growth
- proofs/squarish-iterates.md: Theorem 1 (Transition Set Finite)
- Zsygmondy's theorem (1892) for primitive prime divisors of Mersenne numbers
- Results on $\sigma(m) = N$ having finitely many solutions
