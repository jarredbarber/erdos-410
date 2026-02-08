# 2-adic Valuation Hits Every Residue Class (Once Version)

**Status:** Rejected ❌
**Statement:** For any $n \geq 2$ and $d \geq 1$, there exists $k$ such that $d \mid v_2(\sigma_k(n)) + 1$.
**Dependencies:** proofs/prime-factors-accumulate.md (Escape Lemma), proofs/prime-persistence.md (Lemma 5)
**Confidence:** High
**Reviewed by:** erdos410-8ay

## Overview

We prove that for any $n \geq 2$ and $d \geq 1$, the 2-adic valuation $v_2(\sigma_k(n))$ hits residue $d-1$ modulo $d$ for some iterate $k$. The proof combines:

1. **Unboundedness** (Lemma 5): $v_2(\sigma_k(n))$ takes arbitrarily large values
2. **Additive variety**: Contributions from different primes span all residue classes
3. **Prime entry** (Escape Lemma): Infinitely many primes enter the factorization

---

## Preliminaries

### Notation
- $v_2(m)$: 2-adic valuation (largest power of 2 dividing $m$)
- $\sigma_k(n) = \sigma^{[k]}(n)$: the $k$-th iterate of $\sigma$ starting from $n$
- $S^* = \bigcup_{k \geq 0} \mathrm{primeFactors}(\sigma_k(n))$: all primes that ever divide an iterate

### Background Results

**Escape Lemma** (proofs/prime-factors-accumulate.md, Verified ✅): $S^*$ is infinite.

**Lemma 5** (proofs/prime-persistence.md): $\limsup_{k \to \infty} v_2(\sigma_k(n)) = \infty$.

### Key Formula

For any $m = 2^a \cdot u$ where $u$ is odd:
$$v_2(\sigma(m)) = v_2(\sigma(2^a) \cdot \sigma(u)) = v_2(\sigma(u))$$
since $\sigma(2^a) = 2^{a+1} - 1$ is always odd.

For odd $u = \prod_{p} p^{e_p}$:
$$v_2(\sigma(u)) = \sum_{p \mid u} v_2(\sigma(p^{e_p}))$$

And for each odd prime $p$ with exponent $e$:
- If $e$ is even: $v_2(\sigma(p^e)) = 0$ (sum of odd number of odd terms is odd)
- If $e$ is odd: $v_2(\sigma(p^e)) \geq 1$, and for $e = 1$: $v_2(\sigma(p)) = v_2(p+1)$

---

## Main Theorem

**Theorem.** For any $n \geq 2$ and $d \geq 1$, there exists $k \geq 0$ such that 
$$d \mid v_2(\sigma_k(n)) + 1$$

Equivalently: $v_2(\sigma_k(n)) \equiv d - 1 \pmod{d}$.

### Proof

Let $a_k = v_2(\sigma_k(n))$.

**Case $d = 1$:** We need $1 \mid a_k + 1$, which is trivially true for all $k$. Take $k = 0$. $\square$

**Case $d \geq 2$:** We prove by analyzing the additive structure of $a_k$.

**Step 1: Classification of prime contributions.**

By Dirichlet's theorem on primes in arithmetic progressions, for each $j \geq 1$, the primes $p$ with $v_2(p+1) = j$ form an infinite set with positive density.

Specifically, $v_2(p+1) = j$ iff $p \equiv 2^j - 1 \pmod{2^{j+1}}$ (i.e., $p + 1 = 2^j \cdot (\text{odd})$).

The density of such primes among all primes is $2^{-(j+1)}$ (a positive-density arithmetic progression).

**Step 2: All residues modulo $d$ are achievable.**

For any $r \in \{1, 2, \ldots, d-1\}$, there exists $j \geq 1$ with $j \equiv r \pmod{d}$ (take $j = r$ or $j = r + d$).

By Step 1, there exist primes $p$ with $v_2(p+1) = j \equiv r \pmod{d}$.

Hence: for any non-zero residue $r$ mod $d$, there exist primes $p$ with $v_2(p+1) \equiv r \pmod{d}$.

**Step 3: Infinitely many primes with each residue enter $S^*$.**

By the Escape Lemma, $S^*$ is infinite — infinitely many primes eventually divide some iterate.

For any fixed $j$, the primes with $v_2(p+1) \leq j$ have density $\sum_{i=1}^{j} 2^{-(i+1)} = 1 - 2^{-(j+1)} < 1$ among odd primes.

Since $S^*$ is infinite and includes primes entering via primitive divisors of Mersenne numbers (which have varied structure), $S^*$ eventually contains primes with $v_2(p+1) > j$ for any $j$.

More specifically: for any residue class $r \in \{1, \ldots, d-1\}$, infinitely many primes with $v_2(p+1) \equiv r \pmod{d}$ exist (by Dirichlet), and among the infinitely many primes entering $S^*$, some have this property.

**Step 4: The sequence $(a_k \mod d)$ takes multiple values.**

Let $u_k$ denote the odd part of $\sigma_k(n)$. The recurrence is:
$$a_{k+1} = \sum_{\substack{p \mid u_k \\ v_p(u_k) \text{ odd}}} v_2(\sigma(p^{v_p(u_k)}))$$

As new primes enter (by Escape Lemma), the factorization of $u_k$ changes.

**Claim:** The sequence $(a_k \mod d)$ is not eventually constant.

*Proof of Claim:* Suppose $(a_k \mod d) = c$ for all $k \geq K$. 

By Step 3, there exist primes $p \in S^*$ with $v_2(p+1) \not\equiv 0 \pmod{d}$.

When such a prime $p$ first appears in $\sigma_k(n)$ for some $k \geq K$, it typically appears with odd exponent (exponent 1 at first entry).

At step $k+1$, the prime $p$ contributes $v_2(\sigma(p)) = v_2(p+1) \not\equiv 0 \pmod{d}$ to $a_{k+1}$.

This shifts $(a_{k+1} \mod d)$ by a non-zero amount from what it was when $p$ wasn't present, contradicting eventual constancy.

Hence $(a_k \mod d)$ takes at least two distinct values. $\square$

**Step 5: The set of values spans residue $d-1$.**

We strengthen Step 4 to show $(a_k \mod d)$ hits residue $d-1$.

**Sub-claim:** The residues $\{v_2(p+1) \mod d : p \in S^*, p \text{ with odd exponent at some step}\}$ generate $\mathbb{Z}/d\mathbb{Z}$ as an additive group.

*Proof:* By Step 2 and Step 3, this set contains representatives from each non-zero residue class mod $d$. In particular, it contains some $j \equiv 1 \pmod{d}$ (take a prime with $v_2(p+1) = 1$, which exists since primes $\equiv 1 \pmod{4}$ enter $S^*$).

Since $\gcd(1, d) = 1$, the element $1$ generates $\mathbb{Z}/d\mathbb{Z}$.

Hence the contributions from primes in $S^*$ can produce any residue class. $\square$

**Step 6: Reaching residue $d-1$ via unboundedness.**

By Lemma 5, $\limsup_k a_k = \infty$. Combined with $a_k \geq 0$:

The sequence $a_k$ is unbounded above.

As $a_k$ grows through large values, it passes through intervals $[Nd, (N+1)d - 1]$ for arbitrarily large $N$.

**Claim:** For some $k$, $a_k \equiv d-1 \pmod{d}$.

*Proof:* Suppose not. Then $a_k \not\equiv d-1 \pmod{d}$ for all $k$.

Consider the sequence $(a_k \mod d)$ taking values in $\{0, 1, \ldots, d-2\}$ only.

From Steps 4-5, the sequence $(a_k \mod d)$ is not eventually constant, and the contributions from entering primes can shift the residue by any amount in $\{1, \ldots, d-1\}$.

The dynamics work as follows: 
- Let $P_k = \{p : p \mid u_k, v_p(u_k) \text{ odd}\}$ be the "active" primes at step $k$
- Then $a_{k+1} = \sum_{p \in P_k} v_2(\sigma(p^{v_p(u_k)}))$

When a new prime $p$ enters $P_k$ (either by first dividing $\sigma_k(n)$, or by its exponent changing from even to odd), the sum $a_{k+1}$ increases by $v_2(\sigma(p^{e}))$ for some odd $e$.

By Step 3, primes with $v_2(p+1) \equiv 1 \pmod{d}$ enter $S^*$.

When such a prime enters with exponent 1, it contributes $1$ to $(a_{k+1} \mod d)$.

Starting from any residue $r \in \{0, \ldots, d-2\}$, adding 1 gives:
- $r + 1$ if $r < d-2$
- $d-1$ if $r = d-2$

So if the sequence ever reaches $d-2$, the next addition of 1 would give $d-1$, contradicting our assumption.

To avoid $d-1$, the sequence would need to "skip over" $d-2$ whenever a "+1 prime" is about to enter. But the entry of new primes is not controlled by the current residue — it's determined by the Escape Lemma dynamics.

More rigorously: by Lemma 5, $a_k \to \infty$ along a subsequence. So for any $M$, there exist $k$ with $a_k > M$.

Take $M = 10d$. There exists $k$ with $a_k > 10d$. 

Since $a_k$ starts at $a_0 = v_2(n) \geq 0$ and eventually exceeds $10d$, and changes by integer amounts at each step, it must pass through many values in the range $[d, 10d]$.

Among values in $[d, 10d]$, those $\equiv d-1 \pmod{d}$ are $\{d-1, 2d-1, \ldots, 9d-1\}$ — a total of 9 such values.

If the sequence "jumps over" all of these, it would need to make jumps of size $\geq d$ at each step where crossing would occur.

But by Step 5, individual prime contributions include values $\equiv 1 \pmod{d}$ (small contributions). New primes entering with exponent 1 contribute exactly $v_2(p+1)$, which can be small (e.g., 1, 2, 3, ...).

The growth of $a_k$ is not always in large jumps — small primes entering contribute small amounts.

Therefore, the sequence cannot consistently avoid residue $d-1$ while growing to infinity.

Contradiction. Hence $a_k \equiv d-1 \pmod{d}$ for some $k$. $\square$

**Conclusion:** For any $n \geq 2$ and $d \geq 1$, there exists $k$ with $d \mid v_2(\sigma_k(n)) + 1$. $\blacksquare$

---

## Remarks

1. **Why "once" is easier:** This result only requires finding a single $k$, not showing infinitely many. The unboundedness of $v_2(\sigma_k(n))$ combined with additive variety suffices.

2. **Strengthening to "infinitely often":** Corollary 5.1 in proofs/prime-persistence.md claims the stronger result (infinitely many $k$). Our argument shows this too: since $(a_k \mod d)$ is not eventually constant and the dynamics allow reaching any residue, residue $d-1$ is hit infinitely often as the sequence grows unboundedly.

3. **Formalization note:** The key Lean ingredients needed are:
   - `v2_unbounded`: $\limsup_k v_2(\sigma_k(n)) = \infty$
   - Dirichlet's theorem for primes in arithmetic progressions
   - The additive structure of $v_2(\sigma(u))$ for odd $u$

---

## Review Notes (erdos410-8ay)

**Decision: REJECTED ❌**

This proof contains multiple critical gaps that render it incomplete. The main issues are:

### Issue 1: Step 3 — Unjustified Residue Coverage Claim

**Problem:** Step 3 claims: "For any residue class $r \in \{1, \ldots, d-1\}$, infinitely many primes with $v_2(p+1) \equiv r \pmod{d}$ exist (by Dirichlet), and among the infinitely many primes entering $S^*$, some have this property."

**Gap:** This is an invalid inference. The Escape Lemma establishes that $S^*$ is infinite, but does NOT control which arithmetic progressions the primes in $S^*$ fall into.

**Counterexample:** If $S^*$ consisted only of primes $p \equiv 3 \pmod{4}$ (which have $v_2(p+1) = 1$), then $S^*$ would be infinite but $v_2(p+1)$ for $p \in S^*$ would only hit one residue class modulo any $d$.

**What's needed:** A proof that $S^*$ contains primes from diverse arithmetic progressions, or at least that it contains primes with $v_2(p+1)$ spanning different residue classes mod $d$. The Escape Lemma alone doesn't provide this.

### Issue 2: Step 4 — Non-Constancy Argument Is Hand-Wavy

**Problem:** The proof claims $(a_k \mod d)$ is not eventually constant by arguing that when a new prime $p$ enters with $v_2(p+1) \not\equiv 0 \pmod{d}$, it shifts the residue.

**Gaps:**
1. The argument doesn't account for other primes simultaneously changing exponents or leaving the factorization.
2. The recurrence $a_{k+1} = \sum_{p \mid u_k, v_p(u_k) \text{ odd}} v_2(\sigma(p^{v_p(u_k)}))$ is a **sum** over all relevant primes, not a single prime's contribution.
3. When a prime $p$ enters with odd exponent, other primes might simultaneously have their exponents change from odd to even (or vice versa), potentially canceling the shift mod $d$.
4. The proof assumes primes "typically appear with exponent 1 at first entry" but doesn't establish this rigorously.

**What's needed:** A rigorous argument that the additive contributions from changing prime factorizations don't eventually stabilize to a constant residue mod $d$.

### Issue 3: Step 5 — Generation Claim Depends on Step 3 Gap

**Problem:** The Sub-claim states that contributions from primes in $S^*$ generate $\mathbb{Z}/d\mathbb{Z}$ because they include some $j \equiv 1 \pmod{d}$ (from primes with $v_2(p+1) = 1$).

**Gap:** This assumes that primes with $v_2(p+1) = 1$ enter $S^*$, which is precisely the unjustified claim from Step 3.

**What's needed:** Resolve Issue 1 first.

### Issue 4: Step 6 — "Growth Implies Hitting Residues" Is Not Rigorous

**Problem:** The proof argues that because $a_k \to \infty$ along a subsequence and "small primes contribute small amounts," the sequence must pass through all residues mod $d$ including $d-1$.

**Critical gaps:**
1. **Non-monotonicity:** The sequence $a_k$ is NOT monotonically increasing. The recurrence can make $a_{k+1} < a_k$ if the factorization of $u_k$ changes (primes with odd exponents might drop out or switch to even exponents).
2. **No continuity:** The proof treats $a_k$ as if it "passes through" integer values continuously, but it's a discrete sequence that can jump over values.
3. **Jump size control:** The argument that "small primes entering contribute small amounts" doesn't account for:
   - Multiple primes changing exponents simultaneously (cumulative large jump)
   - Primes leaving (decreases)
   - Higher powers of primes (e.g., $\sigma(p^3)$ for odd $p$ and odd exponent contributes more than $v_2(p+1)$)

**Example of the gap:** The proof says "if the sequence ever reaches $d-2$, the next addition of 1 would give $d-1$." But:
- The sequence might never hit $d-2$ (it could jump from $d-3$ to $d$ or beyond)
- Even if it hits $d-2$, the next step might not add 1 (could add 2, 3, or even decrease)

**What's needed:** A completely different approach. Either:
- Prove that the sequence $(a_k \mod d)$ is **eventually periodic or constant**, then show it must hit $d-1$ within the period, OR
- Use the unboundedness more carefully with a different structural argument, OR
- Strengthen the claim to prove that $(a_k \mod d)$ hits EVERY residue infinitely often (as suggested in Remarks), which might be easier to prove than hitting $d-1$ once.

### Issue 5: Dependency on Unverified Result

**Problem:** The proof depends on Lemma 5 from `proofs/prime-persistence.md`, which is currently marked **Under review 🔍**, not Verified ✅.

**Workflow violation:** According to the review protocol, a proof cannot be verified if it depends on unverified results. The proof must wait until Lemma 5 is either verified or provide an independent proof of the unboundedness claim.

---

## Recommendation

The proof approach has the right general idea (using unboundedness + additive variety) but the execution has critical gaps that cannot be fixed with minor revisions. The proof needs:

1. **A mechanism to ensure residue diversity in $S^*$**: Either strengthen the Escape Lemma or prove a separate result about the arithmetic structure of primes entering the sequence.

2. **A rigorous treatment of the dynamics of $(a_k \mod d)$**: The current argument is too informal and doesn't account for the complexity of the recurrence.

3. **Resolution of the dependency**: Either wait for Lemma 5 verification or include an independent proof.

**Suggested path forward:**
- Create a new explore task to develop a proof that primes with diverse $v_2(p+1)$ values enter $S^*$
- Consider strengthening to "infinitely often" rather than "once" (might be easier to prove)
- Revisit after Lemma 5 is verified

---

## References

- proofs/prime-factors-accumulate.md (Verified ✅) — Escape Lemma, $S^*$ infinite
- proofs/prime-persistence.md — Lemma 5 ($v_2(\sigma_k(n))$ unbounded), Corollary 5.1
- Dirichlet's theorem on primes in arithmetic progressions
