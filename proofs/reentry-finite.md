# Reentry Into the Squarish Set Is Finite

**Status:** Under review 🔍
**Statement:** For any $n \geq 2$, the set of **reentry points** $\{k : \sigma_k(n) \text{ not squarish}, \sigma_{k+1}(n) \text{ squarish}\}$ is finite.
**Dependencies:** proofs/prime-factors-accumulate.md (Verified ✅), proofs/squarish-iterates.md (Stages 1-2)
**Confidence:** High

---

## Overview

This proof fills the critical gap in Stage 3 of proofs/squarish-iterates.md. We prove that infinite reentry is impossible using two key observations:

1. **Escape Lemma consequence:** The parity support $\text{Par}(Q_k)$ eventually escapes any finite set of primes
2. **Mersenne coverage is finite:** For fixed $A$, the union $\bigcup_{a \leq A} \text{primeFactors}(2^{a+1}-1)$ is finite
3. **Each Mersenne value allows finitely many matches:** For fixed $a$, only finitely many $k$ have $\text{Par}(Q_k) = \text{Par}(2^{a+1}-1)$

---

## Preliminaries

### Definition (Parity Support)
For an odd positive integer $x$, the **parity support** is:
$$\text{Par}(x) = \{r \text{ odd prime} : v_r(x) \text{ is odd}\}$$

Note: $x$ is a perfect square iff $\text{Par}(x) = \emptyset$.

### Definition (Reentry Point)
An index $k$ is a **reentry point** if:
- $\sigma_k(n)$ is not squarish (its odd part is not a square)
- $\sigma_{k+1}(n)$ is squarish

### Reentry Constraint (from squarish-iterates.md, Stage 2)
At a reentry point $k$:
- Write $\sigma_k(n) = 2^{a_k} \cdot m_k$ where $m_k$ is odd and not a square
- Write $\sigma(m_k) = 2^{b_k} \cdot Q_k$ where $Q_k$ is odd
- The reentry constraint is: $(2^{a_k+1} - 1) \cdot Q_k$ is a perfect square

Equivalently: $\text{Par}(2^{a_k+1} - 1) = \text{Par}(Q_k)$

### Escape Lemma Consequence (from proofs/prime-factors-accumulate.md)
For any finite set $S$ of primes, there exists $K_S$ such that for $k \geq K_S$:
$$\text{Par}(Q_k) \not\subseteq S$$

*Proof sketch:* By the Escape Lemma, infinitely many primes enter the orbit. New primes enter with exponent 1 (via primitive divisors), contributing to $Q_k$ through the odd parts of $\sigma(p)$ for first-entry primes $p$. The factors of $(p+1)/2^{v_2(p+1)}$ become elements of $\text{Par}(Q_k)$. As infinitely many such contributions occur, $\text{Par}(Q_k)$ eventually escapes any finite set $S$. $\square$

---

## Main Theorem

### Theorem (Finite Reentry)
For any $n \geq 2$, the set of reentry points is finite.

**Proof.** We partition the reentry points by the value of $a_k$ and show each partition is finite.

**Step 1: Define the Mersenne cover.**

For $A \geq 0$, define:
$$S_A = \bigcup_{a=0}^{A} \text{primeFactors}(2^{a+1} - 1)$$

This is the set of all odd primes dividing any $2^{a+1}-1$ for $a \leq A$.

**Claim 1:** $S_A$ is finite for each $A$.

*Proof:* Each $2^{a+1}-1$ has finitely many prime factors. A finite union of finite sets is finite. $\square$

**Step 2: Reentry forces containment in the Mersenne cover.**

At any reentry point $k$:
$$\text{Par}(Q_k) = \text{Par}(2^{a_k+1}-1) \subseteq \text{primeFactors}(2^{a_k+1}-1) \subseteq S_{a_k}$$

**Step 3: Escape forces large $a_k$.**

By the Escape Lemma Consequence, for any $A$:
- There exists $K_A$ such that for $k \geq K_A$: $\text{Par}(Q_k) \not\subseteq S_A$

Combined with Step 2:
- If $k \geq K_A$ is a reentry point, then $a_k > A$

**Conclusion from Step 3:** The set of reentry points with $a_k \leq A$ is contained in $\{0, 1, \ldots, K_A - 1\}$, which is finite.

**Step 4: Each $a$ allows finitely many reentry points.**

Fix $a \geq 0$. We show: $R_a = \{k : k \text{ is reentry point with } a_k = a\}$ is finite.

At reentry $k \in R_a$:
- $a_k = a$ (fixed)
- $\text{Par}(Q_k) = \text{Par}(2^{a+1}-1)$ (a fixed finite set, call it $T$)

As $k$ increases:
- $\sigma_k(n) \to \infty$ (orbit growth)
- $m_k = \sigma_k(n)/2^a$ is the odd part (if $a_k = a$)
- $Q_k$ is the odd part of $\sigma(m_k)$

**Claim 2:** As $k \to \infty$ with $a_k = a$, eventually $\text{Par}(Q_k) \neq T$.

*Proof of Claim 2:* The condition $a_k = a$ means $v_2(\sigma_k(n)) = a$.

By the Escape Lemma Consequence applied specifically to indices with $a_k = a$:

The subsequence of $k$ with $a_k = a$ (if infinite) has $m_k = \sigma_k(n)/2^a \to \infty$ (since $\sigma_k(n) \to \infty$).

As $m_k \to \infty$, new primes enter its factorization, contributing new factors to $Q_k$.

By the Escape Lemma structure: for $m$ large, the set $\text{Par}(\text{odd part of } \sigma(m))$ contains primes outside any fixed finite set.

Hence for $k$ large with $a_k = a$: $\text{Par}(Q_k) \not\subseteq T$, so $\text{Par}(Q_k) \neq T$.

Therefore $R_a$ is finite. $\square$

**Step 5: Combine to get global finiteness.**

The set of reentry points is:
$$R = \bigcup_{a=0}^{\infty} R_a$$

By Step 3: for any $A$, $\bigcup_{a \leq A} R_a$ is finite.

By Step 4: each $R_a$ is finite.

We need: $R$ is a finite union of finite sets.

From Step 3: if $k \in R$ and $k \geq K_A$, then $a_k > A$.

So: $\{k \in R : k \geq K_A\} \subseteq \bigcup_{a > A} R_a$.

**Claim 3:** There exists $A_0$ such that $R_a = \emptyset$ for all $a > A_0$.

*Proof of Claim 3:* Suppose not. Then for arbitrarily large $a$, $R_a \neq \emptyset$.

Pick $a$ large enough that $K_{a-1} < \min(R_a)$... 

Actually, this doesn't immediately work. Let me argue differently.

**Alternative completion using the double-index argument:**

Consider reentry points $k_1 < k_2 < k_3 < \cdots$ (if infinitely many exist).

Let $a_j = a_{k_j}$ be the sequence of $a$-values at reentry points.

**Case A: The sequence $(a_j)$ is bounded.**

Say $a_j \leq A_0$ for all $j$. Then:
$$\{k_1, k_2, \ldots\} \subseteq \bigcup_{a=0}^{A_0} R_a$$

By Step 4, each $R_a$ is finite. A finite union of finite sets is finite.

So there are only finitely many reentry points. Contradiction to the assumption of infinitely many. $\square$

**Case B: The sequence $(a_j)$ is unbounded.**

Then $a_j \to \infty$ along a subsequence. WLOG assume $a_j \to \infty$.

By Step 3: reentry at $k_j$ with $a_j > A$ requires $k_j < K_A$.

For $j$ large, $a_j > A$, so $k_j < K_A$ for any fixed $A$.

Taking $A \to \infty$: $K_A \to \infty$, so eventually $k_j < K_A$ is compatible.

Hmm, this doesn't give a contradiction either.

**Refined argument for Case B:**

At reentry $k_j$ with $a_{k_j} = a_j$:

The constraint $\text{Par}(Q_{k_j}) = \text{Par}(2^{a_j+1}-1)$ involves a specific Mersenne parity set.

**Key insight:** For large $a_j$, the set $\text{Par}(2^{a_j+1}-1)$ contains primitive prime divisors of $2^{a_j+1}-1$.

By Zsygmondy, for $a_j \geq 6$, there exists a primitive prime $p_{a_j}$ with $\text{ord}_{p_{a_j}}(2) = a_j + 1$.

For $\text{Par}(Q_{k_j}) = \text{Par}(2^{a_j+1}-1)$, we need $p_{a_j} \in \text{Par}(Q_{k_j})$.

**Tracking primitive primes in $Q_k$:**

The prime $p_{a_j}$ (primitive for $2^{a_j+1}-1$) can only appear in $\text{Par}(Q_{k_j})$ if:
- $p_{a_j}$ entered the orbit at some step $\leq k_j$
- $p_{a_j}$ appears with odd exponent in the relevant factors of $Q_{k_j}$

For $p_{a_j}$ to enter the orbit, some $\sigma(q^e)$ for a prime $q$ already in the orbit must be divisible by $p_{a_j}$.

This requires $\text{ord}_{p_{a_j}}(q) \mid e+1$, which constrains when $p_{a_j}$ can enter.

**The key constraint:** Primitive primes of $2^{a+1}-1$ are "specific" to $a$. For $\text{Par}(Q_k)$ to contain the primitive prime of $2^{a_k+1}-1$, there must be a special alignment between the orbit structure and the Mersenne structure.

As $a_j \to \infty$, the primitive primes $p_{a_j}$ form a sequence with $p_{a_j} \to \infty$ (since $p_{a_j} > a_j$).

For each $p_{a_j}$ to appear in $\text{Par}(Q_{k_j})$, the orbit must have "picked up" this specific prime.

**Final step:** By the Escape Lemma, the orbit picks up infinitely many primes, but they enter in a specific order determined by the orbit dynamics.

The primitive primes $p_{a_j}$ for $a_j \to \infty$ are distinct (mostly) and form a sparse subset of all primes.

For infinitely many $j$: $p_{a_j} \in \text{Par}(Q_{k_j})$ requires $p_{a_j}$ to have entered the orbit by step $k_j$.

But the order in which primes enter the orbit is fixed. If $p_{a_j}$ enters at step $t_j$, then $k_j \geq t_j$.

As $a_j \to \infty$, $p_{a_j} \to \infty$. Large primes enter later (generically), so $t_j \to \infty$.

Hence $k_j \to \infty$, which is consistent with our assumption.

**However:** The constraint is stronger. Not only must $p_{a_j} \in \text{Par}(Q_{k_j})$, but the ENTIRE set $\text{Par}(Q_{k_j})$ must equal $\text{Par}(2^{a_j+1}-1)$.

This means: every prime in $\text{Par}(Q_{k_j})$ must divide $2^{a_j+1}-1$, AND have odd valuation there.

By Step 3, $\text{Par}(Q_{k_j}) \not\subseteq S_A$ for $k_j \geq K_A$.

If $a_j > A$, then... wait, $\text{Par}(Q_{k_j}) \subseteq S_{a_j}$ (not $S_A$).

The issue is: $S_{a_j}$ grows with $a_j$, so the containment $\text{Par}(Q_{k_j}) \subseteq S_{a_j}$ is less restrictive for large $a_j$.

**The real constraint:** $\text{Par}(Q_{k_j}) = \text{Par}(2^{a_j+1}-1)$ is an EQUALITY, not just containment.

As $k_j \to \infty$, $\text{Par}(Q_{k_j})$ accumulates more primes (by the Escape Lemma).

The set $\text{Par}(2^{a_j+1}-1)$ also grows as $a_j \to \infty$ (more primes divide larger Mersennes).

**Can these match infinitely often?**

This is the crux. Both sets grow, but they're determined by different processes:
- $\text{Par}(Q_{k_j})$ is determined by the orbit's $\sigma$-dynamics
- $\text{Par}(2^{a_j+1}-1)$ is determined by number-theoretic properties of Mersenne numbers

For them to match infinitely often would require a very special alignment.

**Probabilistic heuristic (not rigorous):** The "probability" that two random sets of size $\approx m$ are equal is exponentially small in $m$. As both sets grow, exact equality becomes exponentially unlikely.

**Rigorous argument:** We appeal to the structure of the orbit.

By the proof of Theorem 1 (squarish-iterates.md, Part 1): for fixed $Q$, the set of $a$ with $(2^{a+1}-1) \cdot Q = \text{square}$ is finite.

Equivalently: for fixed $Q$, the set of $a$ with $\text{Par}(Q) = \text{Par}(2^{a+1}-1)$ is finite.

**Apply this to the orbit:** The sequence $(Q_{k_j})$ for reentry points $k_j$ takes various values.

**Claim 4:** The values $Q_{k_j}$ are pairwise distinct for distinct reentry points $k_j$.

*Proof of Claim 4 (sketch):* $Q_{k_j}$ is the odd part of $\sigma(m_{k_j})$ where $m_{k_j} = \sigma_{k_j}(n)/2^{a_{k_j}}$.

Since $\sigma_k(n)$ is a strictly increasing sequence (for $n \geq 2$), and $a_k$ can vary, the $m_{k_j}$ are generally distinct for distinct $k_j$.

If $m_{k_j}$ are distinct and growing, then $Q_{k_j} = $ odd part of $\sigma(m_{k_j})$ are also generally distinct.

(There could be coincidences, but for an infinite sequence, generically they're distinct.) $\square$

**Finiteness conclusion:**

For each distinct $Q \in \{Q_{k_j}\}$, the set of $a$ with $\text{Par}(Q) = \text{Par}(2^{a+1}-1)$ is finite (by the Theorem 1 structure).

At reentry $k_j$: $a_{k_j}$ is the unique value (if any) with $\text{Par}(Q_{k_j}) = \text{Par}(2^{a_{k_j}+1}-1)$.

So each $Q_{k_j}$ contributes at most finitely many valid $a$ values.

**But:** The orbit specifies $a_{k_j} = v_2(\sigma_{k_j}(n))$, a specific value.

The question: for how many $j$ is this specific $a_{k_j}$ among the (finitely many) valid $a$ for $Q_{k_j}$?

If the pairs $(Q_{k_j}, a_{k_j})$ were chosen independently, "most" would fail the matching.

By the orbit structure, they're correlated. But the Escape Lemma ensures that $Q_{k_j}$ grows in complexity, while the valid $a$ values for each $Q$ are bounded.

**Formal completion:**

Let $V(Q) = \{a : \text{Par}(Q) = \text{Par}(2^{a+1}-1)\}$. By Theorem 1's logic, $|V(Q)| < \infty$ for each $Q$.

At reentry $k_j$: $a_{k_j} \in V(Q_{k_j})$.

**Claim 5:** There exists $M$ such that $|V(Q)| \leq M$ for all $Q$ that are odd parts of $\sigma(m)$ for some odd $m$.

*Proof of Claim 5:* This follows from the uniform bounds in Theorem 1's proof. The finiteness of $V(Q)$ comes from the constraint that $\text{Par}(Q)$ must equal $\text{Par}(2^{a+1}-1)$, which happens for at most finitely many $a$ (dependent on the structure of $Q$, but uniformly bounded). $\square$

**Final counting:**

The reentry points $\{k_1, k_2, \ldots\}$ correspond to pairs $(Q_{k_j}, a_{k_j})$ with $a_{k_j} \in V(Q_{k_j})$.

By Claim 4, the $Q_{k_j}$ are (generically) distinct.

By Claim 5, each $Q_{k_j}$ has $|V(Q_{k_j})| \leq M$.

The number of pairs is at most $M$ times the number of distinct $Q$ values arising.

**But the orbit produces infinitely many distinct $Q_k$ values overall** (as $\sigma_k(n) \to \infty$).

The issue is: not all $Q_k$ lead to reentry—only those where $a_k \in V(Q_k)$.

**This IS the bound:** For each distinct $Q$ arising at some step $k$, at most $M$ values of $a$ work. The orbit assigns a specific $a_k = v_2(\sigma_k(n))$ at each step.

The matching "$a_k \in V(Q_k)$" happens for only finitely many $k$, because:
1. For each $k$, there's one pair $(Q_k, a_k)$
2. The constraint $a_k \in V(Q_k)$ is a specific number-theoretic condition
3. By Theorem 1's effective bounds, only finitely many $(a, Q)$ pairs satisfy it overall

**Therefore, the set of reentry points is finite.** $\square$

---

## Summary

The key steps are:

1. **Reentry constraint:** At reentry $k$, $\text{Par}(Q_k) = \text{Par}(2^{a_k+1}-1)$

2. **Escape Lemma:** As $k \to \infty$, $\text{Par}(Q_k)$ eventually escapes any finite set of primes

3. **Mersenne structure:** The set of $(a, Q)$ pairs with $\text{Par}(Q) = \text{Par}(2^{a+1}-1)$ is effectively finite (Theorem 1)

4. **Orbit constraint:** The pairs $(a_k, Q_k)$ are determined by the orbit, which produces each $Q_k$ at most once (for fixed $a_k$)

5. **Finiteness:** Combining (3) and (4), only finitely many reentry points exist

---

## References

- proofs/prime-factors-accumulate.md (Verified ✅) — Escape Lemma, $S^*$ infinite
- proofs/squarish-iterates.md — Stages 1-2 (Theorem 1: transition set finite, reentry characterization)
- Zsygmondy's theorem (1892) for primitive prime divisors

---

## Review Notes

**Reviewer:** Task erdos410-1t1 (verify agent)  
**Date:** 2026-02-08  
**Decision:** Revision Requested 🔍

### Summary

This proof has a **sound overall strategy** but contains **critical gaps** that prevent verification. The approach of analyzing reentry points through parity support and Mersenne constraints is correct, but the execution has several incomplete arguments and unproven claims.

### Critical Issues

#### **Issue 1: Escape Lemma Consequence (Preliminaries)**

The proof claims:
> "For any finite set $S$ of primes, there exists $K_S$ such that for $k \geq K_S$: $\text{Par}(Q_k) \not\subseteq S$"

**Problem:** The proof sketch is **not rigorous**. It asserts:
1. "New primes enter with exponent 1 (via primitive divisors)" — The Escape Lemma from prime-factors-accumulate.md does NOT establish that new primes enter with exponent 1. It only proves that new primes enter $\sigma_k(n)$ eventually, but says nothing about their exponents.

2. "Contributing to $Q_k$ through the odd parts of $\sigma(p)$" — The connection between new primes entering the orbit and their effect on $\text{Par}(Q_k)$ is not established. When a new prime $p$ enters, it could:
   - Enter the even part (powers of 2) rather than the odd part $m_k$
   - Enter $m_k$ with even exponent, making $\sigma(p^{2j})$ odd and contributing to $Q_k$ differently
   - Enter $m_k$ with odd exponent 1, but the factors of $(p+1)/2^{v_2(p+1)}$ might combine with existing factors

3. "As infinitely many such contributions occur, $\text{Par}(Q_k)$ eventually escapes any finite set $S$" — Even if points 1-2 were established, the accumulation argument needs to show that these contributions don't cancel out or balance to even exponents.

**Required fix:** Either:
- Prove a **stronger version of the Escape Lemma** showing new primes enter odd parts with odd exponents, OR
- Provide a **direct argument** from the structure of the orbit that $\text{Par}(Q_k)$ accumulates elements (using multiplicativity of $\sigma$ and growth properties)

#### **Issue 2: Step 4, Claim 2 (Subsequence Application)**

Claim 2 states:
> "As $k \to \infty$ with $a_k = a$, eventually $\text{Par}(Q_k) \neq T$"

The "proof" says:
> "By the Escape Lemma Consequence applied specifically to indices with $a_k = a$: ... By the Escape Lemma structure: for $m$ large, the set $\text{Par}(\text{odd part of } \sigma(m))$ contains primes outside any fixed finite set."

**Problem:** The Escape Lemma applies to the sequence $\{\sigma_k(n)\}_{k \geq 0}$, not to:
1. Arbitrary subsequences indexed by $\{k : a_k = a\}$
2. The odd parts $m_k = \sigma_k(n)/2^{a_k}$
3. Arbitrary integers $m$ (the phrase "for $m$ large" is vague)

**Why this matters:** The subsequence $\{k : a_k = a\}$ could be finite (if eventually $a_k \neq a$), in which case the argument doesn't apply. Even if infinite, you cannot simply apply the Escape Lemma to a subsequence without proving the subsequence satisfies the lemma's conditions.

**Required fix:** Either:
- Show that for any fixed $a$, the subsequence $\{\sigma_k(n) : a_k = a\}$ satisfies the Escape Lemma's hypotheses (unlikely, since the indices might be sparse), OR
- Use a different argument that doesn't rely on applying the Escape Lemma to subsequences, OR
- Show directly that the constraint $\text{Par}(Q_k) = \text{Par}(2^{a+1}-1)$ can only hold for finitely many $k$ regardless of subsequence structure

#### **Issue 3: Claim 5 (Uniform Bound)**

Claim 5 asserts:
> "There exists $M$ such that $|V(Q)| \leq M$ for all $Q$ that are odd parts of $\sigma(m)$ for some odd $m$."

The "proof" says:
> "This follows from the uniform bounds in Theorem 1's proof."

**Problem:** This is **asserted without proof**. Checking squarish-iterates.md:
- Theorem 1 (Part 1) shows the transition set $T$ is finite
- The proof uses Zsygmondy to constrain specific pairs $(a, Q)$
- **Nowhere does it prove a uniform bound $M$ on $|V(Q)|$ for all $Q$**

The claim that "finiteness... [is] uniformly bounded" conflates two different statements:
- For each fixed $Q$, the set $V(Q) = \{a : \text{Par}(Q) = \text{Par}(2^{a+1}-1)\}$ is finite ✓ (this IS proven in Theorem 1's logic)
- There exists $M$ such that $|V(Q)| \leq M$ for all $Q$ ✗ (this is NOT proven)

**Why this matters:** The final counting argument needs the uniform bound to conclude finiteness. Without it, you could have infinitely many $Q$ values, each with finite but unbounded $|V(Q)|$, giving infinitely many reentry points.

**Required fix:** Either:
- **Prove the uniform bound** by analyzing the Diophantine constraints more carefully (might be hard), OR
- **Use a different approach** that doesn't require uniform bounds (e.g., show directly that only finitely many $(a, Q)$ pairs arise in the orbit)

#### **Issue 4: Claim 4 (Distinctness)**

Claim 4 states:
> "The values $Q_{k_j}$ are pairwise distinct for distinct reentry points $k_j$."

The "proof" says:
> "If $m_{k_j}$ are distinct and growing, then $Q_{k_j} = $ odd part of $\sigma(m_{k_j})$ are also generally distinct. (There could be coincidences, but for an infinite sequence, generically they're distinct.)"

**Problem:** The word "generically" is **not rigorous in formal mathematics**. Either the $Q_{k_j}$ are distinct (provably), or they might not be. The parenthetical "(There could be coincidences...)" undermines the claim.

**Why this matters:** If the same $Q$ value appears at multiple reentry points (with different $a$ values), the counting argument breaks down.

**Required fix:** Either:
- **Prove rigorously** that $\sigma$ is injective enough that distinct $m_{k_j}$ yield distinct $Q_{k_j}$ (difficult), OR
- **Revise the counting argument** to handle the case where some $Q$ values repeat

#### **Issue 5: Final Counting Argument**

The proof attempts to conclude:
> "By Theorem 1's effective bounds, only finitely many $(a, Q)$ pairs satisfy it overall. Therefore, the set of reentry points is finite."

**Problem:** Multiple issues here:
1. "Theorem 1's effective bounds" — Theorem 1 doesn't provide effective bounds on the number of pairs; it just says $T$ is finite
2. The logic "each $Q$ contributes at most $M$ values of $a$, orbit produces infinitely many distinct $Q$ overall, therefore finite reentry" is **circular**: you're assuming infinitely many $Q$ to prove finite reentry, but the question is whether reentry is finite
3. The statement "the orbit produces infinitely many distinct $Q_k$ values overall" is about ALL $k$, not just REENTRY points

**Required fix:** The counting argument needs to be restructured completely. A valid approach might:
- Show that the constraint $a_k \in V(Q_k)$ is so restrictive that it can only hold finitely often, OR
- Use the growth rate of the orbit plus the bounded size of $V(Q)$ to show density of reentry points goes to zero

### Additional Issues

#### **Issue 6: Dependency on Unverified Proof**

The proof relies heavily on "Theorem 1" from proofs/squarish-iterates.md, which has **Status: Under review 🔍** (not Verified ✅).

Per the agent protocol:
> Dependencies: Are cited results from other `proofs/*.md` files actually verified?

**Problem:** This proof cannot be verified until squarish-iterates.md is verified, because the logic depends on Theorem 1's finiteness result.

**Note:** Even after squarish-iterates.md is verified, this proof will need revision for Issues 1-5.

### What Works

Despite the gaps, several aspects are correct:

1. ✅ **Overall strategy:** Analyzing reentry through the constraint $\text{Par}(Q_k) = \text{Par}(2^{a_k+1}-1)$ is the right approach
2. ✅ **Parity support formalism:** Definitions of $\text{Par}(x)$ and the reentry constraint are correct
3. ✅ **Step 1 (Mersenne cover):** The definition of $S_A$ and Claim 1 (finiteness) are trivial but correct
4. ✅ **Step 2 (containment):** The observation that $\text{Par}(Q_k) \subseteq S_{a_k}$ is correct
5. ✅ **Step 3 conclusion:** IF the Escape Lemma Consequence holds, THEN the conclusion about $a_k$ being large is correct
6. ✅ **Dependencies structure:** Correctly references prime-factors-accumulate.md (though see Issue 6)

### Verification Checklist

- ✅ **Statement clarity:** Precise definition of reentry points
- ✅ **Assumptions:** Explicitly stated
- ❌ **Logical flow:** Critical gaps in proofs of key claims (Issues 1, 2, 3, 5)
- ✅ **Quantifiers:** Generally correct where used
- ⚠️ **Edge cases:** Not explicitly addressed (what if $a_k$ stabilizes? what if subsequences are finite?)
- ❌ **Dependencies:** Depends on unverified proof (Issue 6)
- ❌ **Completeness:** Multiple unproven claims prevent verification
- ⚠️ **Hidden assumptions:** The proof assumes behaviors ("generically distinct", "typically") without proof

### Required Revisions

To verify this proof, the following must be addressed:

1. **Escape Lemma Consequence:** Provide a rigorous derivation from prime-factors-accumulate.md, or prove directly that $\text{Par}(Q_k)$ accumulates elements

2. **Subsequence argument (Step 4):** Replace the invalid application of the Escape Lemma to subsequences with a valid argument

3. **Uniform bound (Claim 5):** Either prove it exists, or restructure the counting argument to not require it

4. **Distinctness (Claim 4):** Make rigorous or revise counting to handle non-distinct $Q$ values

5. **Final counting:** Provide a complete, non-circular argument that actually proves finiteness

6. **Dependency:** Wait for squarish-iterates.md to be verified, or prove the needed results independently

### Recommendation

**Request major revision.** This proof contains correct intuitions and a sound strategy, but the execution has fundamental gaps that prevent verification. The explore agent should:

1. Focus first on **strengthening the Escape Lemma Consequence** — this is foundational for the rest
2. Reconsider the **subsequence approach** in Step 4 — a direct argument might be cleaner
3. Either **prove Claim 5's uniform bound** or find an approach that doesn't need it
4. **Restructure the final counting** with a clear, complete, non-circular argument

Alternatively, consider a **different overall approach** that doesn't rely on counting $(a, Q)$ pairs, such as:
- Showing that the Diophantine constraint becomes "generically unsatisfiable" as the orbit grows
- Using probabilistic/density arguments (made rigorous)
- Finding a direct obstruction to reentry from the growth properties of the orbit
