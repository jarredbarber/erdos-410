# timtam Task: Formalize prime_persistence: close sorry at Basic.lean:799 (erdos410-zp6)

Role: formalize
Agent: formalize (anthropic/claude-opus-4-6:high)
Start Time: 2026-02-08T01:09:25.640Z

## Agent Interaction





> **Thinking:**
> Let me start by understanding the current state of the codebase and the task at hand. I need to close the `prime_persistence` sorry at Basic.lean line 799.
> 
> Let me first read the relevant files to understand the context.


🛠️ **Executing tool: read**

🛠️ **Executing tool: read**


> **Thinking:**
> Let me understand the current state:
> 
> 1. The `prime_persistence` lemma at line ~799 has a `sorry` that needs to be closed.
> 2. The NL proof is long and complex, and the reviewer noted that Issue 4 (permanence for odd primes) is NOT fully resolved.
> 3. The task says I MAY decompose into helper lemmas with sorrys.
> 
> Let me first check the current state of compilation and understand what exactly is needed.
> 
> The lemma statement is:
> ```lean
> lemma prime_persistence (q : ℕ) (hq : Nat.Prime q) (n : ℕ) (hn : n ≥ 2) :
>     ∃ K, ∀ k ≥ K, q ∣ (sigma 1)^[k] n
> ```
> 
> Looking at the code, `prime_persistence` is used by `prime_factors_accumulate` which is already proven (modulo `prime_persistence`'s sorry). So closing the sorry in `prime_persistence` would close the chain.
> 
> Given the complexity of the NL proof and the fact that the reviewer flagged remaining gaps, the best strategy is to decompose `prime_persistence` into sub-lemmas with sorrys, making progress while maintaining compilation. I'll break this down into smaller pieces that each handle a specific aspect of the proof.
> 
> For the even case, the key insight is that σ(m) is odd exactly when m is squarish, and since squarish iterates are finite by Zsygmondy, eventually the iterates stop being squarish and σ becomes even. For odd primes, I need to use the 2-adic mechanism where the order of 2 modulo q determines the periodicity of divisibility.
> 
> Let me focus on what I can actually formalize and introduce sorrys where needed. First, I should check what compiles.


```bash
$ cd /home/jarred/code/erdos-410 && lake build 2>&1 | tail -20
```


> **Thinking:**
> Good, the project builds successfully with only one sorry warning at line 797 (the `prime_persistence` lemma). Let me now plan my approach.
> 
> The task decomposition strategy from the task description suggests:
> 1. `prime_persistence_two (n : ℕ) (hn : n ≥ 2) : ∃ K, ∀ k ≥ K, 2 ∣ (sigma 1)^[k] n`
> 2. `prime_persistence_odd (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) (n : ℕ) (hn : n ≥ 2) : ∃ K, ∀ k ≥ K, q ∣ (sigma 1)^[k] n`
> 
> 
> Then I'll combine them together.
> 
> For the even case, the strategy relies on showing there are only finitely many squarish numbers in the σ-iterate sequence, and after that point all subsequent values are even by the `sigma_even_of_not_squarish` lemma. The finiteness part using Zsygmondy is the tricky piece, so I'll leave that as a sorry for now. The odd prime case is more involved with a known gap, so I'll also leave that as sorry since the task allows introducing new sorrys in sub-lemmas.
> 
> Let me start by setting up the lemma structure...
> 
> Defining the lemmas for the two and odd cases...
> 
> Now I'm completing the main prime persistence lemma by handling both cases - when the prime is 2 and when it's odd. I'm using the existing `Nat.Prime.eq_two_or_odd` tactic to split on whether the prime equals 2, then delegating to the appropriate specialized lemma for each case.
> 
> Looking more carefully at how this works: the odd case gives me `q % 2 = 1`, which I can use to derive `q ≠ 2` since 2's remainder is 0. For the parts I can actually prove without sorry, the combination logic should be straightforward, and I might be able to make progress on `prime_persistence_two` as well.
> 
> The strategy would be to establish that iterates of the sigma function eventually stop being squarish, then use that to show divisibility by 2 holds eventually.
> 
> Completing the proof structure...
> 
> I need to convert `Even` to divisibility. The `even_iff_two_dvd` lemma should bridge these two concepts, so I can rewrite the even condition and apply the divisibility result directly. I'm trying to figure out the right lemma to convert from `Even (sigma 1 n)` to `2 ∣ sigma 1 n`. The `even_iff_two_dvd.mp` function should work for this conversion, though I'm also seeing `Even.two_dvd` used elsewhere in the codebase, so let me verify which one is the right approach here.
> 
> Rather than getting stuck on the exact lemma name, I should just try implementing the proof and see if it compiles. My plan is to structure the proof in stages: first add a lemma about squarish iterates being finite with a sorry, then prove the two case for prime persistence from that, add the odd case with a sorry, and finally combine both cases into the main result.
> 
> Writing the proof structure... I'm establishing that the previous iterate isn't squarish, then using that fact along with a non-zero condition to derive that sigma of the previous iterate is even, which means 2 divides the current iterate by the successor property.
> 
> Now I need to handle the general case for odd primes—I'll split on whether q equals 2, then prove that for any odd prime, there's eventually a point where q always divides the iterated sigma function. I think `omega` should handle this since it can work with modular arithmetic—if `q % 2 = 1` and `q = 2`, that would give `0 = 1`, a contradiction. Let me write out the full proof and test it, then check whether Zsygmondy's theorem or a similar result is available in Mathlib for the `prime_persistence_two` path.


```bash
$ cd /home/jarred/code/erdos-410 && grep -r "Zsygmondy\|zsygmondy\|primitive.*prime.*divisor\|bang.*theorem" .lake/packages/mathlib/Mathlib/ --include="*.lean" -l 2>/dev/null | head -10
```

```bash
$ cd /home/jarred/code/erdos-410 && grep -rn "squarish\|IsSquarish\|prime_persistence\|squarish_iterates" Erdos/Basic.lean | head -20
```
Zs

> **Thinking:**
> ygmondy's theorem is not in Mathlib. So `squarish_iterates_finite` will need to stay as a sorry.
> 
> Let me now update the task status and proceed with the decomposition.
> 
> Let me write the decomposed code. I'll need to:
> 1. Add `squarish_iterates_finite` with sorry before `prime_persistence`
> 2. Add `prime_persistence_two` proved from it
> 3. Add `prime_persistence_odd` with sorry
> 4. Prove `prime_persistence` from the two cases
> 
> Let me find the exact location in the file to add these lemmas.


```bash
$ cd /home/jarred/code/erdos-410 && tm update erdos410-zp6 --status "Decomposing prime_persistence into sub-lemmas with case split on q=2 vs q odd"
```

🛠️ **Executing tool: read**


> **Thinking:**
> Now let me write the decomposed code. I'll replace the sorry in `prime_persistence` with a case split that uses two new sub-lemmas.
> 
> Let me write the new code:

Now I have a clear picture. Let me write the decomposition. I'll add the sub-lemmas before `prime_persistence` and then prove it by combining them.
🛠️ **Executing tool: edit**

```bash
$ cd /home/jarred/code/erdos-410 && lake build 2>&1 | tail -20
```


> **Thinking:**
> The `conv_lhs` tactic is not working because the goal is `2 ∣ (sigma 1)^[k] n`, not a pattern where I can easily rewrite `k`. Let me fix this.
> 
> The issue is that I need to show `2 ∣ (sigma 1)^[k] n` and I have `Even (sigma 1 ((sigma 1)^[k-1] n))`. Since `(sigma 1)^[k] n = sigma 1 ((sigma 1)^[k-1] n)` when `k = (k-1) + 1`, I need to rewrite.
> 
> 
> I should try using `simp` with the `pow_succ` lemma to unfold the iterated function application, then apply the evenness property directly to the result.


🛠️ **Executing tool: edit**

```bash
$ cd /home/jarred/code/erdos-410 && lake build 2>&1 | tail -15
```
The

> **Thinking:**
>  issue is that `simp` after rewriting `k = (k-1) + 1` expands `Function.iterate_succ` differently - it puts it as `f^[k-1] (f n)` rather than `f (f^[k-1] n)`. Let me use `Function.iterate_succ'` directly with `rw`.


🛠️ **Executing tool: edit**

```bash
$ cd /home/jarred/code/erdos-410 && lake build 2>&1 | tail -10
```


> **Thinking:**
> The issue is that `rw [this]` rewrites `k` everywhere, including in `(sigma 1)^[k-1]` on the RHS, creating `(sigma 1)^[k-1+1-1]`. Let me rethink.The goal is: `2 ∣ (sigma 1)^[k] n`I know: `heven : Even (sigma 1 ((sigma 1)^[k-1] n))`I need to rewrite `(sigma 1)^[k] n` to `sigma 1 ((sigma 1)^[k-1] n)`.Let me try using `show` or `suffices`:


🛠️ **Executing tool: edit**

```bash
$ cd /home/jarred/code/erdos-410 && lake build 2>&1 | tail -10
```
Let

> **Thinking:**
>  me try a simpler approach. I'll directly convert the proof to work by showing `k = (k-1) + 1` and then using `Function.iterate_succ_apply'` or computing it manually.
> 
> Actually, let me just do:
> ```lean
>   obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
> ```
> 
> Then `k = j + 1` and `k - 1 = j`, and the goal becomes `2 ∣ (sigma 1)^[j+1] n` which is `2 ∣ sigma 1 ((sigma 1)^[j] n)`.


🛠️ **Executing tool: edit**

```bash
$ cd /home/jarred/code/erdos-410 && lake build 2>&1 | tail -10
```
The

> **Thinking:**
>  build succeeds with only sorry warnings for `squarish_iterates_finite` (line 791) and `prime_persistence_odd` (line 824). The main `prime_persistence` lemma now has no sorry — it's proven from the two sub-lemmas.
> 
> Now let me commit this and then see if I can make further progress on the sub-lemmas.
> 
> Let me first verify the sorry locations:

Build succeeds. The main `prime_persistence` sorry is now closed, decomposed into two sub-lemma sorrys. Let me commit and then try to make further progress.
```bash
$ cd /home/jarred/code/erdos-410 && git add -A && git commit -m "Decompose prime_persistence into case split: q=2 (squarish) and q odd

- prime_persistence is now sorry-free, proven by case split
- prime_persistence_two: proven from squarish_iterates_finite  
- squarish_iterates_finite: sorry (needs Zsygmondy's theorem)
- prime_persistence_odd: sorry (needs 2-adic valuation argument)"
```

```bash
$ cd /home/jarred/code/erdos-410 && tm update erdos410-zp6 --status "prime_persistence closed (case split). Now trying to further decompose sub-lemmas."
```
Now let me try to go deeper. Let me look at what additional sub-structure I can formalize. Let me start with the easier pieces — the `squarish_iterates_finite` case.

The NL proof's key idea for `squarish_iterates_finite` is that if m is squarish with m = 2^a · t² (t odd), then:
σ(m) = σ(2^a) · σ(t²) = (2^{a+1} - 1) · σ(t²)

This product is odd (since both factors are odd). For σ(m) to also be squarish, the odd number (2^{a+1} - 1) · σ(t²) must be a perfect square. This is constrained by Zsygmondy.

The simplest approach for further decomposition: I need Zsygmondy's theorem (not in Mathlib). Let me instead think of a weaker approach that might work. 

Actually, let me try a different angle entirely for both sub-lemmas. Instead of formalizing the full NL proof details (which requires Zsygmondy), let me see if there's a simpler self-contained argument.

Let me search for alternative approaches:
```bash
$ cd /home/jarred/code/erdos-410 && grep -rn "multiplicitiveOrder\|orderOf\|ZMod.orderOf\|Nat.Mpl" .lake/packages/mathlib/Mathlib/NumberTheory/ --include="*.lean" -l 2>/dev/null | head -10
```

```bash
$ cd /home/jarred/code/erdos-410 && grep -rn "orderOf" .lake/packages/mathlib/Mathlib/GroupTheory/Order* --include="*.lean" -l 2>/dev/null | head -10
```

```bash
$ cd /home/jarred/code/erdos-410 && grep -rn "geomSum_dvd\|geom_sum_dvd\|dvd_geom" .lake/packages/mathlib/Mathlib/ --include="*.lean" | head -10
```


> **Thinking:**
> Let me focus on the odd prime case which is actually simpler and more self-contained. The NL proof's key idea for odd q is:
> 
> 1. The 2-adic valuation of σ_k(n) is unbounded
> 2. When d = ord_q(2) divides (a_k + 1), then q | σ(2^{a_k}) 
> 3. This gives q | σ_{k+1}(n) infinitely often
> 4. Once q is present, it persists
> 
> Steps 1-3 give "q enters infinitely often", and step 4 gives permanence.
>  
> Rather than tackle the full argument at once, I should break down both `squarish_iterates_finite` and `prime_persistence_odd` into smaller, more manageable lemmas. For `prime_persistence_odd`, I can decompose it into pieces like a lemma stating that q divides σ_k(n) for infinitely many k, which captures the core behavior I need. The persistence lemma is actually the trickiest part to prove. Let me reconsider what's tractable—for the q=2 case with squarish iterates, I could try a different angle using the structural constraints that arise when consecutive iterates are both squarish. If σ_k(n) has the form 2^a · t² with t odd, then σ(σ_k(n)) being squarish while σ_k(n) is already squarish creates very restrictive conditions on the factorization.
> 
> The issue is that Zsygmondy's theorem would give me what I need about primitive prime divisors, but without it in Mathlib I'm stuck. Maybe I should focus on proving prime persistence directly instead of trying to establish that squarish iterates must be finite—that might be a more tractable path forward.
> 
> The key realization is that once an iterate becomes even but not squarish, all subsequent iterates stay even. So I really just need to show that eventually some iterate hits this state. Let me trace through a concrete example: starting with n = 2, I get σ(2) = 3, then σ(3) = 4, which is even and not squarish, so from there the chain stays even. So the challenge is proving that squarish numbers don't form infinite σ-chains for any starting point n ≥ 2. Rather than tackle that directly, I think the better approach is to mark `squarish_iterates_finite` and `prime_persistence_odd` as sorrys for now and create separate tasks for them—this breaks down the main `prime_persistence` problem into two cleaner subproblems. For the odd prime case specifically, I'm wondering if there's a more tractable way to decompose it further based on what the NL proof suggests.
> 
> Looking at the dependency structure, `prime_persistence` sits at the foundation with everything else downstream depending on it, so I need to be careful about circular reasoning. The key insight for odd q is that 2 eventually always divides σ_k(n) from the two-case result, and the iterates tend toward infinity, but I'm still working through how to formalize this cleanly without relying on the main result itself.
> 
> Let me trace through the 2-adic valuation more carefully. The recurrence shows v_2(σ_{k+1}(n)) depends on the odd part of σ_k(n), and for odd primes p, I need to understand how σ(p^e) behaves to determine whether the 2-adic valuation stays bounded or grows unbounded. I'm realizing the NL proof doesn't actually rely on prime persistence for the 2-adic unboundedness—it uses σ_k(n) → ∞ and the Escape Lemma independently. The real issue is that `prime_factors_accumulate` depends on `prime_persistence`, so I need to break that circular dependency by finding what I can prove directly without assuming prime persistence.
> 
> Looking at what's available: σ_k(n) grows unbounded, σ is odd exactly for squarish numbers, and multiplicativity from Mathlib. For odd primes, I'm trying a direct approach—since σ_k(n) gets arbitrarily large, there should be enough "room" for any prime q to eventually divide some σ_k(n), though I need to make this rigorous rather than just relying on size.
> 
> Given how tangled this is getting, I think the pragmatic path forward is to close the main `prime_persistence` sorry by breaking it into smaller lemmas, then tackle `squarish_iterates_finite` and `prime_persistence_odd` separately. For the squarish case specifically, I'm thinking about how if m = 2^a · t² with t odd, then σ(m) = (2^{a+1} - 1) · σ(t²), and for this to remain squarish when it's odd, it would need to be a perfect square—that's the key constraint to formalize.
> 
> Actually, I'm realizing I shouldn't over-decompose here. These two remaining sorrys are already well-scoped: one depends on Zsygmondy's theorem which isn't in Mathlib, and the other is a genuinely hard number-theoretic argument. Rather than fragmenting further, I should acknowledge these are legitimate hard lemmas that will require either proving Zsygmondy in Lean or finding a different mathematical approach entirely.
> 
> Now I'm wondering if I can actually prove the odd persistence property using what's available in Mathlib. The core idea is that for an odd prime q dividing σ(2^a) = 2^{a+1} - 1, the divisibility depends on whether the multiplicative order of 2 modulo q divides a+1. Since Fermat's little theorem bounds this order by q-1, I could potentially use a pigeonhole argument: if the 2-adic valuations keep growing unboundedly, then infinitely many of them must fall into the same residue class modulo some divisor, forcing infinitely many to satisfy the divisibility condition.
> 
> But here's the problem—I need to establish that v_2(σ_k(n)) is actually unbounded. I know σ_k(n) grows without limit and is always even for large k, but that doesn't automatically mean the power of 2 dividing it keeps increasing. A number like 2p can be arbitrarily large while having v_2 = 1, so I'm stuck without a stronger argument about how the 2-adic valuation itself behaves.
> 
> Let me try a different approach. Instead of proving v_2 unboundedness first, can I use the fact that σ_k(n) → ∞ directly to establish prime_persistence_odd? The key insight is that as σ_k(n) grows, it must accumulate infinitely many distinct prime divisors. By Dirichlet's theorem, among these primes, infinitely many satisfy p ≡ 1 (mod q) for any given prime q. Once I have such a prime p dividing some σ_k(n), I can use σ(p) = 1 + p to continue the chain.
> 
> The challenge is that when p appears in σ_k(n), it might have exponent greater than 1, or it might share factors with other parts of the factorization, which complicates the multiplicativity argument for σ. I need to carefully track how the prime factors propagate through the σ function to ensure q actually divides σ_{k+1}(n). q divides σ_{k+1}(n). The real challenge is whether we can always find some prime p ≡ 1 (mod q) that appears with exponent q-1 modulo q. When a prime first shows up at step k, its exponent in σ_k(n) is typically just 1, but that only satisfies our divisibility condition when q = 2. For odd q, I need e+1 ≡ 0 (mod q), meaning e ≡ q-1, which e = 1 doesn't provide.
> 
> The exponent would need to grow through the iteration process, but tracking whether that happens reliably is getting quite intricate. Let me refocus on what I can actually establish here.
> 
> I've closed `prime_persistence` through case analysis, which is solid progress. Two sorrys remain: `squarish_iterates_finite` and `prime_persistence_odd`, both of which depend on deeper number-theoretic results that aren't readily in Mathlib. I'm exploring whether I can break `prime_persistence_odd` into smaller, more structured pieces—like establishing that the 2-adic valuation grows unboundedly through iteration...
> 
> Writing Lean lemmas... I see the lemma signature is incomplete, so let me finish it: the goal is to show that if a prime q divides σ(n) infinitely often along the iteration sequence, then it must divide σ(n) for all sufficiently large iterations. Now I'm thinking about how to prove `q_dvd_sigma_two_pow` using the multiplicative order — the key insight is that σ(2^a) = 2^{a+1} - 1, so q divides this exactly when the order of 2 modulo q divides a+1, which I can establish using ZMod properties.

Let me explore what Mathlib API is available for the key mathematical components:
```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_order.lean << 'EOF'
import Mathlib

-- Check orderOf in ZMod
#check @orderOf (ZMod _) _ _
#check ZMod.orderOf_dvd_iff
#check orderOf_dvd_iff_pow_eq_one
#check ZMod.val_natCast
EOF
lake env lean /tmp/test_order.lean 2>&1 | head -20
```

```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_order2.lean << 'EOF'
import Mathlib

-- q | 2^{a+1} - 1 iff ord_q(2) | (a+1)
-- In ZMod q: 2^{a+1} = 1 iff ord_q(2) | (a+1)
-- And 2^{a+1} ≡ 1 (mod q) iff q | 2^{a+1} - 1

#check ZMod.natCast_zmod_eq_zero_iff_dvd
#check Nat.sub_one_eq_pred
-- For σ(2^a) = 2^{a+1} - 1:
-- #check ArithmeticFunction.sigma_apply_prime_pow

-- For the geom sum:
#check Nat.geomSum_eq

-- ZMod.units
#check ZMod.unitOfCoprime
EOF
lake env lean /tmp/test_order2.lean 2>&1 | head -20
```

```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_order3.lean << 'EOF'
import Mathlib

-- Key bridge: q | 2^(a+1) - 1 iff (2 : ZMod q)^(a+1) = 1
-- Then orderOf_dvd_iff_pow_eq_one gives ord_q(2) | (a+1)

-- Need: q | 2^(a+1) - 1 ↔ (2 : ZMod q)^(a+1) = 1
#check ZMod.natCast_zmod_eq_zero_iff_dvd  -- might be gone 
#check ZMod.natCast_eq_zero
-- ah maybe:
example (q : ℕ) (hq : q ≠ 0) (a : ℕ) : q ∣ a ↔ (a : ZMod q) = 0 := by
  exact_mod_cast (ZMod.natCast_zmod_eq_zero_iff_dvd a q).symm
EOF
lake env lean /tmp/test_order3.lean 2>&1 | head -20
```

```bash
$ cd /home/jarred/code/erdos-410 && grep -rn "natCast.*zmod.*eq.*zero\|natCast.*eq_zero" .lake/packages/mathlib/Mathlib/Data/ZMod/ --include="*.lean" | head -10
```

```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_order4.lean << 'EOF'
import Mathlib

-- The key lemma we need
#check ZMod.natCast_eq_zero_iff

-- Bridge: q | 2^(a+1) - 1 relates to (2 : ZMod q)^(a+1) = 1
-- 2^(a+1) - 1 ≡ 0 (mod q) iff 2^(a+1) ≡ 1 (mod q) 

-- Can we get: q | (2^n - 1) iff (2 : ZMod q)^n = 1?
-- First: q | m iff (m : ZMod q) = 0
-- So: q | (2^n - 1) iff (2^n - 1 : ZMod q) = 0 iff (2 : ZMod q)^n = 1

-- sigma_pow_two' already exists in our codebase
-- sigma 1 (2^k) = 2^(k+1) - 1

-- For q | sigma 1 (2^a):
-- q | 2^(a+1) - 1
-- iff (2^(a+1) - 1 : ZMod q) = 0  [by ZMod.natCast_eq_zero_iff]
-- iff (2 : ZMod q)^(a+1) = 1  [since 2^(a+1) ≥ 1]
-- iff orderOf (2 : ZMod q) ∣ (a+1)  [by orderOf_dvd_iff_pow_eq_one]

-- Let's verify the cast works
example (q : ℕ) (n : ℕ) (h : n ≥ 1) : 
    (q ∣ n - 1) ↔ ((n : ZMod q) = 1) := by
  sorry
  
-- Actually let me check Nat.cast_sub
#check @Nat.cast_sub
EOF
lake env lean /tmp/test_order4.lean 2>&1 | head -20
```

```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_order5.lean << 'EOF'
import Mathlib

open ArithmeticFunction

-- q | sigma 1 (2^a) iff orderOf (2 : ZMod q) | (a + 1), for q prime and q ≠ 2
-- sigma 1 (2^a) = 2^(a+1) - 1 by sigma_pow_two' (in our codebase)
-- q | 2^(a+1) - 1 iff (2^(a+1) : ZMod q) = 1

-- Step 1: q | 2^n - 1 iff (2 : ZMod q)^n = 1  (for q ≥ 2)
lemma dvd_two_pow_sub_one_iff (q n : ℕ) (hq : q ≥ 2) (hn : n ≥ 1) :
    q ∣ 2^n - 1 ↔ (2 : ZMod q)^n = 1 := by
  have h2n_pos : 2^n ≥ 1 := Nat.one_le_pow n 2 (by omega)
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h2n_pos]
  push_cast
  constructor
  · intro h; linarith [h]
  · intro h; linarith [h]

-- Step 2: (2 : ZMod q)^n = 1 iff orderOf (2 : ZMod q) | n
-- This is just orderOf_dvd_iff_pow_eq_one

-- Combine:
lemma q_dvd_sigma_two_pow_iff (q a : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    q ∣ 2^(a+1) - 1 ↔ orderOf (2 : ZMod q) ∣ (a + 1) := by
  rw [dvd_two_pow_sub_one_iff q (a+1) (by omega) (by omega)]
  exact orderOf_dvd_iff_pow_eq_one.symm
EOF
lake env lean /tmp/test_order5.lean 2>&1 | head -30
```


> **Thinking:**
> The cast approach is tricky. Let me try a different approach.The issue is converting between `q ∣ 2^n - 1` (in ℕ) and `(2 : ZMod q)^n = 1`.In ZMod q:- `(2^n - 1 : ZMod q) = 0` iff `q ∣ 2^n - 1`
> - `(2^n - 1 : ZMod q) = (2 : ZMod q)^n - 1` (cast of subtraction, careful with ℕ vs ℤ)
> 
> 
> The key is handling the subtraction carefully—in ℕ it's natural subtraction, but in ZMod I need ring subtraction. Let me work directly in ZMod q: since `2^n ≥ 1`, the divisibility `q ∣ (2^n - 1)` in ℕ translates to `((2^n - 1 : ℕ) : ZMod q) = 0`.
> 
> I can use `Nat.cast_sub` to show that `((2^n - 1 : ℕ) : ZMod q) = (2 : ZMod q)^n - 1`, and since ZMod q is a CommRing with AddGroupWithOne, this cast should work cleanly.


```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_order6.lean << 'EOF'
import Mathlib

-- q | 2^n - 1 iff (2 : ZMod q)^n = 1
lemma dvd_two_pow_sub_one_iff (q n : ℕ) (hq : q ≥ 2) :
    q ∣ 2^n - 1 ↔ (2 : ZMod q)^n = 1 := by
  have h2n_pos : 2^n ≥ 1 := Nat.one_le_pow n 2 (by omega)
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h2n_pos]
  simp [sub_eq_zero]
EOF
lake env lean /tmp/test_order6.lean 2>&1 | head -20
```


> **Thinking:**
> It works. Let me now build the full lemma for `q ∣ sigma 1 (2^a)`:

That works. Now let me build the full chain:
```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_order7.lean << 'EOF'
import Mathlib

open ArithmeticFunction

-- From our codebase
lemma sigma_pow_two' (k : ℕ) : sigma 1 (2^k) = 2^(k+1) - 1 := by
  rw [sigma_apply_prime_pow (Nat.prime_two)]
  have h : ∀ j, 2^(j * 1) = 2^j := fun j => by ring_nf
  simp_rw [h]
  have hgs := Nat.geomSum_eq (by norm_num : (2 : ℕ) ≤ 2) (k + 1)
  have h2 : (2 : ℕ) - 1 = 1 := by norm_num
  rw [h2, Nat.div_one] at hgs
  exact hgs

-- q | 2^n - 1 iff (2 : ZMod q)^n = 1
lemma dvd_two_pow_sub_one_iff (q n : ℕ) :
    q ∣ 2^n - 1 ↔ (2 : ZMod q)^n = 1 := by
  have h2n_pos : 2^n ≥ 1 := Nat.one_le_pow n 2 (by omega)
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h2n_pos]
  simp [sub_eq_zero]

-- q | sigma 1 (2^a) iff orderOf (2 : ZMod q) | (a + 1)
lemma q_dvd_sigma_two_pow_iff (q a : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    q ∣ sigma 1 (2^a) ↔ orderOf (2 : ZMod q) ∣ (a + 1) := by
  rw [sigma_pow_two', dvd_two_pow_sub_one_iff]
  exact orderOf_dvd_iff_pow_eq_one.symm

-- orderOf (2 : ZMod q) ≥ 1 for odd prime q (since 2 ≠ 1 in ZMod q when q > 2)
lemma orderOf_two_pos (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    orderOf (2 : ZMod q) ≥ 1 := by
  have h : orderOf (2 : ZMod q) ≠ 0 := by
    intro h
    have : IsOfFinOrder (2 : ZMod q) := by
      exact isOfFinOrder_of_finite (2 : ZMod q)
    rw [isOfFinOrder_iff_orderOf_pos] at this
    omega
  omega

-- If d | (a+1) for some a where v_2(σ_k(n)) = a, then q | σ(2^a) | σ_{k+1}(n)
-- The key is: σ(n) is multiplicative, and 2^a || σ_k(n) means σ_k(n) = 2^a * m with m odd
-- Then σ(σ_k(n)) = σ(2^a) * σ(m) when gcd(2^a, m) = 1

-- Check if we can get q | σ(n) from q | σ(2^a) when 2^a | n
-- This requires: n = 2^a * m with gcd(2^a, m) = 1

EOF
lake env lean /tmp/test_order7.lean 2>&1 | head -20
```

```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_order8.lean << 'EOF'
import Mathlib

-- orderOf (2 : ZMod q) ≥ 1 for prime q > 2
lemma orderOf_two_pos (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    orderOf (2 : ZMod q) ≥ 1 := by
  -- (2 : ZMod q) has finite order since ZMod q is finite
  -- orderOf > 0 for elements in finite groups
  have hfin : 0 < Fintype.card (ZMod q) := by simp [ZMod.card q]; exact hq.pos
  have := orderOf_pos (2 : ZMod q)
  omega
EOF
lake env lean /tmp/test_order8.lean 2>&1 | head -20
```


> **Thinking:**
> The issue is that `ZMod q` for a general variable `q` doesn't synthesize `Fintype` or `LeftCancelMonoid` automatically. We need `Fact (Nat.Prime q)` or `NeZero q` instances. Let me fix this.


```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_order9.lean << 'EOF'
import Mathlib

-- orderOf (2 : ZMod q) ≥ 1 for prime q > 2
lemma orderOf_two_pos (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    orderOf (2 : ZMod q) ≥ 1 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  -- ZMod q is a field when q is prime
  -- (2 : ZMod q) ≠ 0 since q > 2
  have h2ne : (2 : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h; exact hodd (Nat.eq_of_dvd_of_lt h (by omega) |>.symm)
  have h2ne1 : (2 : ZMod q) ≠ 1 := by
    sorry
  -- In a finite group, orderOf > 0
  have : 0 < orderOf (2 : ZMod q) := by
    exact orderOf_pos (2 : ZMod q)
  omega
EOF
lake env lean /tmp/test_order9.lean 2>&1 | head -20
```

```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_order10.lean << 'EOF'
import Mathlib

-- (2 : ZMod q) ≠ 0 for prime q > 2
lemma two_ne_zero_zmod (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    (2 : ZMod q) ≠ 0 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  intro h
  have : q ∣ 2 := by rwa [ZMod.natCast_zmod_eq_zero_iff_dvd] at h
  exact hodd (Nat.eq_of_dvd_of_lt this (by omega) |>.symm)

#check @orderOf_pos_iff
-- Hmm, the issue is LeftCancelMonoid. For ZMod q when q is prime, 
-- we need to work with the units group or use Field properties.

-- Actually let me try using (ZMod q)ˣ
-- Or just use the fact that ZMod q is an integral domain

-- For fields/integral domains, ZMod q should have LeftCancelMonoid via IsDomain
-- Actually ZMod q for prime q is a Field, hence an IsDomain
-- IsDomain has NoZeroDivisors, which gives cancellation for multiplication
-- But orderOf is for the additive or multiplicative monoid...

-- Actually orderOf is in the multiplicative monoid
-- For ZMod q as multiplicative monoid with q prime:
-- ZMod q is a CommMonoidWithZero, and also a GroupWithZero
-- GroupWithZero gives cancellation

-- Let me check
example (q : ℕ) (hq : Nat.Prime q) : GroupWithZero (ZMod q) := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  exact ZMod.instGroupWithZero

-- So ZMod q is a GroupWithZero. But is it a LeftCancelMonoid?
-- GroupWithZero implies monoid but not necessarily LeftCancelMonoid
-- because 0 * a = 0 * b but a ≠ b is possible

-- The trick: work with (ZMod q)ˣ instead, or use orderOf on (ZMod q)ˣ
-- Or use the additive group structure?

-- Actually, let me look at what orderOf needs
#check @orderOf_pos -- needs LeftCancelMonoid
-- Hmm

-- Alternative: work with ZMod.unitOfCoprime
-- Since 2 is coprime to q (when q is odd prime), we can get 2 as a unit
example (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) : (ZMod q)ˣ := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  exact ZMod.unitOfCoprime 2 (by
    rw [Nat.coprime_comm]
    exact (Nat.Coprime.prime_dvd_iff_eq (Nat.coprime_two_left.mpr (Nat.Prime.odd_of_ne_two hq hodd)) hq).not.mp (by omega) |>.elim
  )

-- Actually this is getting complicated. Let me just prove it differently.
-- For the multiplicative group (ZMod q)ˣ, orderOf always works.

-- Key fact: for a unit u in a finite group, orderOf u > 0
-- (ZMod q)ˣ is a finite group when q is prime

EOF
lake env lean /tmp/test_order10.lean 2>&1 | head -20
```

```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_order11.lean << 'EOF'
import Mathlib

-- Let me search for the right API
#check ZMod.natCast_eq_zero_iff  -- (a : ZMod n) = 0 ↔ n ∣ a
-- Actually let me search with exact?

-- Key goal: orderOf (2 : ZMod q) > 0 when q is an odd prime
-- Since (ZMod q) for prime q is a field, and fields have IsDomain
-- But orderOf_pos needs LeftCancelMonoid...

-- Alternative approach: use orderOf_pos_iff and show IsOfFinOrder
example (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    orderOf (2 : ZMod q) ≥ 1 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, orderOf_pos_iff]
  exact isOfFinOrder_of_finite _

-- Check if ZMod q is Finite when q is prime
-- It should be since ZMod q = Fin q for q > 0
EOF
lake env lean /tmp/test_order11.lean 2>&1 | head -20
```

```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_order12.lean << 'EOF'
import Mathlib

example (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    orderOf (2 : ZMod q) ≥ 1 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have h : 0 < orderOf (2 : ZMod q) := by
    rw [orderOf_pos_iff]
    exact isOfFinOrder_of_finite _
  omega

-- Now the key lemma: q | sigma 1 (2^a) iff orderOf (2 : ZMod q) | (a+1)
-- We already have sigma 1 (2^a) = 2^(a+1) - 1

-- q | 2^n - 1 iff (2 : ZMod q)^n = 1
lemma dvd_two_pow_sub_one_iff (q n : ℕ) :
    q ∣ 2^n - 1 ↔ (2 : ZMod q)^n = 1 := by
  have h2n_pos : 2^n ≥ 1 := Nat.one_le_pow n 2 (by omega)
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h2n_pos]
  simp [sub_eq_zero]

-- Main: if orderOf (2 : ZMod q) | (a+1), then q | sigma 1 (2^a)
-- And sigma 1 (2^a) = 2^(a+1) - 1
lemma sigma_pow_two'_val (k : ℕ) : ArithmeticFunction.sigma 1 (2^k) = 2^(k+1) - 1 := by
  rw [ArithmeticFunction.sigma_apply_prime_pow (Nat.prime_two)]
  have h : ∀ j, 2^(j * 1) = 2^j := fun j => by ring_nf
  simp_rw [h]
  have hgs := Nat.geomSum_eq (by norm_num : (2 : ℕ) ≤ 2) (k + 1)
  have h2 : (2 : ℕ) - 1 = 1 := by norm_num
  rw [h2, Nat.div_one] at hgs
  exact hgs

-- Now combine: q | sigma 1 (2^a) ↔ orderOf (2 : ZMod q) | (a + 1)
lemma q_dvd_sigma_two_pow_iff (q a : ℕ) :
    q ∣ ArithmeticFunction.sigma 1 (2^a) ↔ orderOf (2 : ZMod q) ∣ (a + 1) := by
  rw [sigma_pow_two'_val, dvd_two_pow_sub_one_iff]
  exact orderOf_dvd_iff_pow_eq_one.symm

-- Now: if σ_k(n) = 2^a * m with m odd and gcd(2^a, m) = 1,
-- then σ(σ_k(n)) = σ(2^a) * σ(m) by multiplicativity
-- If q | σ(2^a), then q | σ(σ_k(n))

-- So: if orderOf (2 : ZMod q) | (v_2(σ_k(n)) + 1), then q | σ_{k+1}(n)

-- For this to give persistence, we need v_2(σ_k(n)) + 1 to hit multiples of d = orderOf(2 : ZMod q)
-- This requires v_2(σ_k(n)) to be unbounded (or hit specific residues)

EOF
lake env lean /tmp/test_order12.lean 2>&1 | head -10
```

```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_order13.lean << 'EOF'
import Mathlib

example (q : ℕ) (hq : Nat.Prime q) :
    orderOf (2 : ZMod q) ≥ 1 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have h : 0 < orderOf (2 : ZMod q) := by
    rw [orderOf_pos_iff]
    exact isOfFinOrder_of_finite (2 : ZMod q)
  omega
EOF
lake env lean /tmp/test_order13.lean 2>&1 | head -10
```
The problem is that `is

> **Thinking:**
> OfFinOrder_of_finite` requires `Finite` and `Monoid`, but for `orderOf_pos_iff` we need `Monoid`, not `LeftCancelMonoid`. However, the `IsOfFinOrder` approach seems to have a different issue.Let me try a different route: work with units of ZMod q.


```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_units.lean << 'EOF'
import Mathlib

-- Work with (ZMod q)ˣ for the order theory
-- For q prime, (ZMod q)ˣ is a finite group of order q-1

-- Can we lift 2 to (ZMod q)ˣ?
-- Yes, when q is odd prime, gcd(2,q) = 1

example (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    IsUnit (2 : ZMod q) := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  rw [ZMod.isUnit_prime_iff_not_dvd hq]
  intro h2q
  interval_cases q <;> simp_all

-- orderOf for units works in finite groups
-- orderOf in (ZMod q)ˣ equals orderOf in ZMod q when 2 is a unit

-- Actually, let me use a different approach: 
-- orderOf_pos for Monoid needs LeftCancelMonoid
-- But I can show IsOfFinOrder directly

-- Actually for CommMonoidWithZero that is also a GroupWithZero...
-- hmm

-- Let me try: since 2 is a unit, orderOf (IsUnit.unit ...) > 0
-- and orderOf u = orderOf (IsUnit.unit u) ... ?

-- Actually the key fact:
#check orderOf_pos_iff
-- orderOf_pos_iff : 0 < orderOf x ↔ IsOfFinOrder x
-- This needs Monoid, not LeftCancelMonoid!

-- And IsOfFinOrder in a Monoid (ZMod q) for a finite type:
-- IsOfFinOrder means ∃ n > 0, x^n = 1

-- For a unit: its order divides the group order, hence finite
-- isOfFinOrder_of_finite needs Finite and Monoid

-- But ZMod q IS a Monoid (it's a CommRing)
-- And ZMod q IS Finite when q > 0

-- Let me check if Lean can synthesize these
example (q : ℕ) (hq : Nat.Prime q) :
    @Finite (ZMod q) := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  -- ZMod q for q > 0 is Fin q, which is finite
  haveI : NeZero q := ⟨hq.ne_zero⟩
  exact ZMod.instFinite q

example (q : ℕ) (hq : Nat.Prime q) :
    @Monoid (ZMod q) := by
  exact CommMonoidWithZero.toMonoid

-- Wait, Monoid from CommMonoidWithZero... but the problem is that
-- isOfFinOrder_of_finite requires Monoid AND Finite, and orderOf_pos_iff
-- only requires Monoid.

-- But earlier we got "failed to synthesize LeftCancelMonoid"
-- That was from orderOf_pos, not orderOf_pos_iff!

-- Let me try orderOf_pos_iff directly
example (q : ℕ) (hq : Nat.Prime q) :
    0 < orderOf (2 : ZMod q) := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  rw [orderOf_pos_iff]
  exact isOfFinOrder_of_finite (2 : ZMod q)
EOF
lake env lean /tmp/test_units.lean 2>&1 | head -20
```


> **Thinking:**
> The issue is that `isOfFinOrder_of_finite` apparently requires `LeftCancelMonoid` too, or the Lean doesn't know `ZMod q` is finite.
> 
> Let me check what `isOfFinOrder_of_finite` requires exactly:


```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_fin.lean << 'EOF'
import Mathlib

#check @isOfFinOrder_of_finite
-- Check: this should tell us the exact typeclass requirements
EOF
lake env lean /tmp/test_fin.lean 2>&1 | head -5
```


> **Thinking:**
> Ah, `isOfFinOrder_of_finite` requires `LeftCancelMonoid`, not just `Monoid`. And ZMod q with multiplication is NOT a LeftCancelMonoid because 0 * anything = 0.
> 
> I need to work with units instead. Let me use `(ZMod q)ˣ` which IS a finite group.
> 
> Let me think about how to relate `orderOf` in `(ZMod q)ˣ` to divisibility by q.
> 
> Actually, let me think differently. The condition `(2 : ZMod q)^n = 1` already implies that `orderOf (2 : ZMod q)` divides n by `orderOf_dvd_of_pow_eq_one`. And for the converse, `pow_orderOf_eq_one` gives `(2 : ZMod q)^(orderOf (2 : ZMod q)) = 1`, and then if `orderOf | n`, we get `(2 : ZMod q)
> 
> ^n = 1`.
> 
> But I should verify whether these lemmas also require LeftCancelMonoid or if they work more generally.


```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_fin2.lean << 'EOF'
import Mathlib

#check @orderOf_dvd_of_pow_eq_one
#check @pow_orderOf_eq_one
#check @orderOf_dvd_iff_pow_eq_one
EOF
lake env lean /tmp/test_fin2.lean 2>&1
```


> **Thinking:**
> `orderOf_dvd_iff_pow_eq_one` only needs `Monoid`, which is great! And ZMod q is a Monoid (it's a CommRing). So `dvd_two_pow_sub_one_iff` combined with `orderOf_dvd_iff_pow_eq_one` should give us what we need.
> 
> The issue was only with `orderOf_pos` which needs `LeftCancelMonoid`. But we don't actually need `orderOf_pos` for the main argument. Let me verify the key lemmas compile:


```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_full.lean << 'EOF'
import Mathlib

open ArithmeticFunction

-- q | 2^n - 1 iff (2 : ZMod q)^n = 1
lemma dvd_two_pow_sub_one_iff (q n : ℕ) :
    q ∣ 2^n - 1 ↔ (2 : ZMod q)^n = 1 := by
  have h2n_pos : 2^n ≥ 1 := Nat.one_le_pow n 2 (by omega)
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h2n_pos]
  simp [sub_eq_zero]

-- sigma 1 (2^k) = 2^(k+1) - 1 (from codebase, repeated here for test)
lemma sigma_pow_two'_test (k : ℕ) : sigma 1 (2^k) = 2^(k+1) - 1 := by
  rw [sigma_apply_prime_pow (Nat.prime_two)]
  have h : ∀ j, 2^(j * 1) = 2^j := fun j => by ring_nf
  simp_rw [h]
  exact Nat.geomSum_eq (by norm_num) (k + 1) |>.mp rfl |>.mp rfl |> by
    have hgs := Nat.geomSum_eq (by norm_num : (2 : ℕ) ≤ 2) (k + 1)
    simp at hgs; exact hgs

-- q | sigma 1 (2^a) ↔ orderOf (2 : ZMod q) | (a + 1)
lemma q_dvd_sigma_two_pow_iff' (q a : ℕ) :
    q ∣ sigma 1 (2^a) ↔ orderOf (2 : ZMod q) ∣ (a + 1) := by
  rw [sigma_pow_two'_test, dvd_two_pow_sub_one_iff]
  exact orderOf_dvd_iff_pow_eq_one.symm
  
EOF
lake env lean /tmp/test_full.lean 2>&1 | head -20
```

```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_full2.lean << 'EOF'
import Mathlib

open ArithmeticFunction

-- q | 2^n - 1 iff (2 : ZMod q)^n = 1
lemma dvd_two_pow_sub_one_iff (q n : ℕ) :
    q ∣ 2^n - 1 ↔ (2 : ZMod q)^n = 1 := by
  have h2n_pos : 2^n ≥ 1 := Nat.one_le_pow n 2 (by omega)
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h2n_pos]
  simp [sub_eq_zero]

-- sigma 1 (2^k) = 2^(k+1) - 1 (from codebase)
lemma sigma_pow_two'_test (k : ℕ) : sigma 1 (2^k) = 2^(k+1) - 1 := by
  rw [sigma_apply_prime_pow (Nat.prime_two)]
  have h : ∀ j, 2^(j * 1) = 2^j := fun j => by ring_nf
  simp_rw [h]
  have hgs := Nat.geomSum_eq (by norm_num : (2 : ℕ) ≤ 2) (k + 1)
  have h2 : (2 : ℕ) - 1 = 1 := by norm_num
  rw [h2, Nat.div_one] at hgs
  exact hgs

-- q | sigma 1 (2^a) ↔ orderOf (2 : ZMod q) | (a + 1)
lemma q_dvd_sigma_two_pow_iff' (q a : ℕ) :
    q ∣ sigma 1 (2^a) ↔ orderOf (2 : ZMod q) ∣ (a + 1) := by
  rw [sigma_pow_two'_test, dvd_two_pow_sub_one_iff]
  exact orderOf_dvd_iff_pow_eq_one.symm
  
EOF
lake env lean /tmp/test_full2.lean 2>&1 | head -10
```
Excellent! Both lemmas compile. Now let me also verify that `orderOf (2 : ZMod q) ≥ 1` for prime q ≠ 2, since we'll need this:
```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_ord_pos.lean << 'EOF'
import Mathlib

-- For odd prime q, orderOf (2 : ZMod q) ≥ 1
-- Strategy: 2 is a unit in ZMod q, so it has positive order in the units group
-- Then its order in the monoid agrees
lemma orderOf_two_zmod_pos (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    orderOf (2 : ZMod q) ≥ 1 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  -- Since q is odd prime, 2 is coprime to q
  have hcop : Nat.Coprime 2 q := by
    rw [Nat.coprime_comm]
    exact hq.coprime_iff_not_dvd.mpr (fun h => hodd (Nat.le_of_dvd (by omega) h |>.antisymm (Nat.Prime.two_le hq)))
  -- Lift 2 to a unit
  let u : (ZMod q)ˣ := ZMod.unitOfCoprime 2 hcop
  -- The order of u in (ZMod q)ˣ is positive (finite group)
  have hu_pos : 0 < orderOf u := orderOf_pos u
  -- The order of u in (ZMod q)ˣ equals the order of (↑u : ZMod q) in ZMod q
  have h_eq : orderOf (u : ZMod q) = orderOf u := by
    exact (IsUnit.orderOf_eq_orderOf ⟨u, rfl⟩).symm
  -- And (↑u : ZMod q) = 2
  have hu_val : (u : ZMod q) = 2 := by
    simp [u, ZMod.IsUnit_IsUnit_eq_val]
    sorry -- need to show the coercion equals 2
  rw [← hu_val, h_eq]
  omega
EOF
lake env lean /tmp/test_ord_pos.lean 2>&1 | head -20
```

```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_ord_pos2.lean << 'EOF'
import Mathlib

-- Alternative approach: show (2 : ZMod q)^(q-1) = 1 by Fermat's little theorem
-- Then orderOf divides (q-1), which is ≥ 1

-- For prime q, ZMod q is a field, and Fermat's little theorem says a^(q-1) = 1 for a ≠ 0

lemma orderOf_two_zmod_pos (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    orderOf (2 : ZMod q) ≥ 1 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  -- 2 ≠ 0 in ZMod q since q > 2
  have h2ne : (2 : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    exact hodd (Nat.le_of_dvd (by omega) hdvd |>.antisymm hq.two_le)
  -- By Fermat's little theorem: 2^(q-1) = 1 in ZMod q
  have hfermat : (2 : ZMod q)^(q - 1) = 1 := by
    have := ZMod.pow_card_sub_one_eq_one h2ne
    exact this
  -- orderOf divides q-1
  have hdvd := orderOf_dvd_of_pow_eq_one hfermat
  -- q-1 ≥ 1
  have hq1 : q - 1 ≥ 1 := by omega
  -- orderOf ≥ 1
  exact Nat.one_le_iff_ne_zero.mpr (fun h => by simp [h] at hdvd; omega)
EOF
lake env lean /tmp/test_ord_pos2.lean 2>&1 | head -10
```

```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_ord_pos3.lean << 'EOF'
import Mathlib

-- (2 : ZMod q) ≠ 0 for odd prime q
lemma two_ne_zero_zmod (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    (2 : ZMod q) ≠ 0 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩  
  -- 2 = (2 : ℕ) cast to ZMod q
  -- (2 : ZMod q) = 0 iff q | 2
  have : (2 : ZMod q) = ((2 : ℕ) : ZMod q) := by norm_cast
  rw [this, Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  exact hodd (Nat.le_of_dvd (by omega) hdvd |>.antisymm hq.two_le)

lemma orderOf_two_zmod_pos (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    orderOf (2 : ZMod q) ≥ 1 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have h2ne := two_ne_zero_zmod q hq hodd
  have hfermat : (2 : ZMod q)^(q - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  have hdvd := orderOf_dvd_of_pow_eq_one hfermat
  exact Nat.one_le_iff_ne_zero.mpr (fun h => by simp [h] at hdvd; omega)
EOF
lake env lean /tmp/test_ord_pos3.lean 2>&1 | head -10
```

```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_ord_pos4.lean << 'EOF'
import Mathlib

lemma two_ne_zero_zmod (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    (2 : ZMod q) ≠ 0 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩  
  have : (2 : ZMod q) = ((2 : ℕ) : ZMod q) := by norm_cast
  rw [this, Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  exact hodd (Nat.le_of_dvd (by omega) hdvd |>.antisymm hq.two_le)

lemma orderOf_two_zmod_pos (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    orderOf (2 : ZMod q) ≥ 1 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have h2ne := two_ne_zero_zmod q hq hodd
  have hfermat : (2 : ZMod q)^(q - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  have hdvd := orderOf_dvd_of_pow_eq_one hfermat
  -- hdvd : orderOf (2 : ZMod q) ∣ (q - 1), and q - 1 ≥ 1
  have hq1 : q - 1 ≥ 1 := by omega
  exact Nat.pos_of_div_pos (Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (by omega)) |>.le |> by
    omega
EOF
lake env lean /tmp/test_ord_pos4.lean 2>&1 | head -10
```

```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_ord_pos5.lean << 'EOF'
import Mathlib

lemma two_ne_zero_zmod (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    (2 : ZMod q) ≠ 0 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩  
  have : (2 : ZMod q) = ((2 : ℕ) : ZMod q) := by norm_cast
  rw [this, Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  exact hodd (Nat.le_of_dvd (by omega) hdvd |>.antisymm hq.two_le)

lemma orderOf_two_zmod_pos (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    orderOf (2 : ZMod q) ≥ 1 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have h2ne := two_ne_zero_zmod q hq hodd
  have hfermat : (2 : ZMod q)^(q - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  have hdvd := orderOf_dvd_of_pow_eq_one hfermat
  -- hdvd : orderOf (2 : ZMod q) ∣ (q - 1), and q - 1 ≥ 1
  -- orderOf ∣ (q-1) and q-1 ≥ 1 implies orderOf ≥ 1
  rcases hdvd with ⟨c, hc⟩
  -- hc : q - 1 = orderOf (2 : ZMod q) * c
  by_contra h
  push_neg at h
  -- orderOf = 0
  simp_all
  omega
EOF
lake env lean /tmp/test_ord_pos5.lean 2>&1 | head -10
```

```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_ord_pos6.lean << 'EOF'
import Mathlib

lemma two_ne_zero_zmod (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    (2 : ZMod q) ≠ 0 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩  
  have : (2 : ZMod q) = ((2 : ℕ) : ZMod q) := by norm_cast
  rw [this, Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  exact hodd (Nat.le_of_dvd (by omega) hdvd |>.antisymm hq.two_le)

lemma orderOf_two_zmod_pos (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    orderOf (2 : ZMod q) ≥ 1 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have h2ne := two_ne_zero_zmod q hq hodd
  have hfermat : (2 : ZMod q)^(q - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  have hdvd := orderOf_dvd_of_pow_eq_one hfermat
  -- If orderOf = 0, then 0 | (q-1), so q-1 = 0, so q = 1, contradiction with prime
  by_contra h
  push_neg at h
  interval_cases (orderOf (2 : ZMod q))
  · -- orderOf = 0 means 0 ∣ (q-1), i.e. q - 1 = 0
    simp at hdvd; omega
EOF
lake env lean /tmp/test_ord_pos6.lean 2>&1 | head -10
```

```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_ord_pos7.lean << 'EOF'
import Mathlib

lemma two_ne_zero_zmod (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    (2 : ZMod q) ≠ 0 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩  
  have : (2 : ZMod q) = ((2 : ℕ) : ZMod q) := by norm_cast
  rw [this, Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  exact hodd (Nat.le_of_dvd (by omega) hdvd |>.antisymm hq.two_le)

lemma orderOf_two_zmod_pos (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    orderOf (2 : ZMod q) ≥ 1 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have h2ne := two_ne_zero_zmod q hq hodd
  have hfermat : (2 : ZMod q)^(q - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  have hdvd := orderOf_dvd_of_pow_eq_one hfermat
  -- If orderOf were 0, then 0 ∣ (q-1), so q - 1 = 0, contradiction
  have hord_ne_zero : orderOf (2 : ZMod q) ≠ 0 := by
    intro h0
    rw [h0] at hdvd
    -- hdvd : 0 ∣ (q - 1), i.e., q - 1 = 0
    have := Nat.eq_zero_of_dvd_of_lt hdvd (by omega : q - 1 < q)
    omega
  omega
EOF
lake env lean /tmp/test_ord_pos7.lean 2>&1 | head -10
```

```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_ord_pos8.lean << 'EOF'
import Mathlib

lemma two_ne_zero_zmod (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    (2 : ZMod q) ≠ 0 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩  
  have : (2 : ZMod q) = ((2 : ℕ) : ZMod q) := by norm_cast
  rw [this, Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  exact hodd (Nat.le_of_dvd (by omega) hdvd |>.antisymm hq.two_le)

lemma orderOf_two_zmod_pos (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    orderOf (2 : ZMod q) ≥ 1 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have h2ne := two_ne_zero_zmod q hq hodd
  have hfermat : (2 : ZMod q)^(q - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  have hdvd := orderOf_dvd_of_pow_eq_one hfermat
  have hord_ne_zero : orderOf (2 : ZMod q) ≠ 0 := by
    intro h0
    rw [h0] at hdvd
    -- 0 ∣ (q - 1) means q - 1 = 0
    have : q - 1 = 0 := Nat.zero_dvd.mp hdvd |>.symm ▸ rfl
    omega
  omega
EOF
lake env lean /tmp/test_ord_pos8.lean 2>&1 | head -10
```

```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_ord_pos9.lean << 'EOF'
import Mathlib

lemma two_ne_zero_zmod (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    (2 : ZMod q) ≠ 0 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩  
  have : (2 : ZMod q) = ((2 : ℕ) : ZMod q) := by norm_cast
  rw [this, Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  exact hodd (Nat.le_of_dvd (by omega) hdvd |>.antisymm hq.two_le)

lemma orderOf_two_zmod_pos (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    orderOf (2 : ZMod q) ≥ 1 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have h2ne := two_ne_zero_zmod q hq hodd
  have hfermat : (2 : ZMod q)^(q - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  have hdvd := orderOf_dvd_of_pow_eq_one hfermat
  have hord_ne_zero : orderOf (2 : ZMod q) ≠ 0 := by
    intro h0
    rw [h0] at hdvd
    -- Now hdvd : 0 ∣ q - 1
    have h01 := Nat.eq_zero_of_zero_dvd hdvd
    omega
  omega
  
-- Check what exists for 0 ∣ n
#check Nat.eq_zero_of_zero_dvd
EOF
lake env lean /tmp/test_ord_pos9.lean 2>&1 | head -10
```


> **Thinking:**
> The issue is that `omega` can't see the `orderOf` term. Let me explicitly convert:


```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_ord_pos10.lean << 'EOF'
import Mathlib

lemma two_ne_zero_zmod (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    (2 : ZMod q) ≠ 0 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩  
  have : (2 : ZMod q) = ((2 : ℕ) : ZMod q) := by norm_cast
  rw [this, Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  exact hodd (Nat.le_of_dvd (by omega) hdvd |>.antisymm hq.two_le)

lemma orderOf_two_zmod_pos (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    orderOf (2 : ZMod q) ≥ 1 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have h2ne := two_ne_zero_zmod q hq hodd
  have hfermat : (2 : ZMod q)^(q - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  have hdvd := orderOf_dvd_of_pow_eq_one hfermat
  -- orderOf ∣ (q - 1), so orderOf ≤ q - 1
  -- Also orderOf ≠ 0 (since 0 ∣ (q-1) → q = 1, contradiction)
  let d := orderOf (2 : ZMod q)
  change d ≥ 1
  have hdvd' : d ∣ q - 1 := hdvd
  have hd_ne_zero : d ≠ 0 := by
    intro h0
    have := Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd' : 0 ∣ q - 1)
    omega
  omega
EOF
lake env lean /tmp/test_ord_pos10.lean 2>&1 | head -10
```


> **Thinking:**
> The problem is that `omega` can't work with `let d := orderOf ...`. Let me try `have` instead and use `show`:


```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_ord_pos11.lean << 'EOF'
import Mathlib

lemma two_ne_zero_zmod (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    (2 : ZMod q) ≠ 0 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩  
  have : (2 : ZMod q) = ((2 : ℕ) : ZMod q) := by norm_cast
  rw [this, Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  exact hodd (Nat.le_of_dvd (by omega) hdvd |>.antisymm hq.two_le)

lemma orderOf_two_zmod_pos (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    orderOf (2 : ZMod q) ≥ 1 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have h2ne := two_ne_zero_zmod q hq hodd
  have hfermat : (2 : ZMod q)^(q - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  have hdvd := orderOf_dvd_of_pow_eq_one hfermat
  exact Nat.pos_of_ne_zero fun h0 => by
    rw [h0] at hdvd
    exact absurd (Nat.eq_zero_of_zero_dvd hdvd) (by omega)
EOF
lake env lean /tmp/test_ord_pos11.lean 2>&1 | head -10
```

```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_ord_pos12.lean << 'EOF'
import Mathlib

-- Simple test: omega with Nat.Prime q
example (q : ℕ) (hq : Nat.Prime q) : q - 1 ≠ 0 := by
  have := hq.two_le; omega

example (q : ℕ) (hq : Nat.Prime q) (h : q - 1 = 0) : False := by
  have := hq.two_le; omega

-- OK so the issue is just connecting the omega-visible facts

lemma two_ne_zero_zmod (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    (2 : ZMod q) ≠ 0 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩  
  have : (2 : ZMod q) = ((2 : ℕ) : ZMod q) := by norm_cast
  rw [this, Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  exact hodd (Nat.le_of_dvd (by omega) hdvd |>.antisymm hq.two_le)

lemma orderOf_two_zmod_pos (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    orderOf (2 : ZMod q) ≥ 1 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have h2ne := two_ne_zero_zmod q hq hodd
  have hfermat : (2 : ZMod q)^(q - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  have hdvd := orderOf_dvd_of_pow_eq_one hfermat
  have hqm1_pos : q - 1 ≠ 0 := by have := hq.two_le; omega
  exact Nat.pos_of_ne_zero fun h0 => hqm1_pos (Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd))
EOF
lake env lean /tmp/test_ord_pos12.lean 2>&1 | head -10
```
All helper lemmas compile. Now let me also think about what further decomposition I can prove for the odd prime case. Let me work on the key lemma that connects 2-adic valuation to q-divisibility:
```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_structure.lean << 'EOF'
import Mathlib

open ArithmeticFunction

-- Key structural lemma: if q | σ(2^a) and 2^a ∥ m (i.e., 2^a | m, m/2^a is odd),
-- then q | σ(m) (via multiplicativity)
-- This is because σ(m) = σ(2^a) * σ(m/2^a) when gcd(2^a, m/2^a) = 1

-- More precisely: for m = 2^a * t with t odd:
-- σ(m) = σ(2^a) * σ(t)
-- So q | σ(2^a) implies q | σ(m)

lemma q_dvd_sigma_of_two_pow_dvd (q a t : ℕ) (hq : q ∣ sigma 1 (2^a)) (ht : Odd t) :
    q ∣ sigma 1 (2^a * t) := by
  by_cases ht0 : t = 0
  · simp [ht0, sigma_apply_zero]
  by_cases ha : a = 0
  · simp [ha]; exact hq
  · have hcop : Nat.Coprime (2^a) t := 
      Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr ht)
    rw [isMultiplicative_sigma.map_mul_of_coprime hcop]
    exact dvd_mul_right q (sigma 1 t) |>.symm ▸ mul_dvd_mul hq (dvd_refl _)

EOF
lake env lean /tmp/test_structure.lean 2>&1 | head -10
```

```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_structure2.lean << 'EOF'
import Mathlib

open ArithmeticFunction

lemma q_dvd_sigma_of_two_pow_dvd (q a t : ℕ) (hq : q ∣ sigma 1 (2^a)) (ht : Odd t) :
    q ∣ sigma 1 (2^a * t) := by
  have hcop : Nat.Coprime (2^a) t := 
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr ht)
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop]
  exact dvd_mul_of_dvd_left hq _
  
EOF
lake env lean /tmp/test_structure2.lean 2>&1 | head -10
```
Now let me think about the full structure for `prime_persistence_odd`. Here's what I can prove:

1. `dvd_two_pow_sub_one_iff` — q | 2^n - 1 ↔ (2 : ZMod q)^n = 1
2. `q_dvd_sigma_two_pow_iff` — q | σ(2^a) ↔ ord_q(2) | (a+1)
3. `q_dvd_sigma_of_two_pow_dvd` — if q | σ(2^a) and t is odd, then q | σ(2^a * t)
4. `orderOf_two_zmod_pos` — ord_q(2) ≥ 1 for prime q ≠ 2

The missing pieces:
- v_2(σ_k(n)) is unbounded (hard, needs Escape Lemma)
- Once q enters, it persists (hard, the reviewer flagged gap)

Let me add all the provable pieces to the codebase and further decompose the remaining sorrys:
🛠️ **Executing tool: read**
Now let me add the helper lemmas and further decompose `prime_persistence_odd`:
🛠️ **Executing tool: edit**

```bash
$ cd /home/jarred/code/erdos-410 && lake build 2>&1 | tail -15
```
Build succeeds. Now let me try to close `prime_enters_infinitely` — this is the most tractable of the remaining sorrys:
```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_enters.lean << 'EOF'
import Mathlib

open ArithmeticFunction

-- We need: ∀ K, ∃ k ≥ K, q ∣ (sigma 1)^[k] n
-- Strategy: 
-- 1. v_2(σ_k(n)) is unbounded (from v2_sigma_iterate_unbounded)
-- 2. Let d = orderOf (2 : ZMod q). Then d ≥ 1.
-- 3. For any K, find k ≥ K with v_2(σ_k(n)) ≥ d-1 and d | (v_2(σ_k(n)) + 1)
-- 4. This is where we need: unbounded v_2 implies we can find one with d | (v_2 + 1)

-- Actually, we need: for any K, there exists k ≥ K such that d | (v_2(σ_k(n)) + 1)
-- This follows from: v_2(σ_k(n)) is unbounded, and for any B, 
-- there exists k with v_2(σ_k(n)) = d*j - 1 for some j, since v_2 ≥ B means it hits d*j - 1

-- Hmm, but "unbounded" doesn't mean it hits every value. It could skip values.
-- We need: for any B, ∃ k, v_2(σ_k(n)) ≥ B AND d | (v_2(σ_k(n)) + 1)

-- Stronger: for any B, ∃ k, v_2(σ_k(n)) + 1 is a multiple of d and ≥ B.
-- This follows from: there exists k with v_2(σ_k(n)) ≥ B*d, 
-- then v_2(σ_k(n)) ≥ d, so v_2(σ_k(n)) + 1 ≥ d+1 > d, 
-- wait, that doesn't help directly.

-- Actually let's think differently. We have σ_k(n) = 2^{a_k} * m_k with m_k odd.
-- We need d | (a_k + 1) for some large k.
-- a_k is unbounded (from v2_sigma_iterate_unbounded).
-- As a_k → ∞ along a subsequence, a_k + 1 takes all large values.
-- Among any d consecutive integers, one is divisible by d.
-- So for a_k + 1 ≥ d, there's... wait, a_k + 1 might not hit all values.

-- The claim is just: there exist infinitely many k with d | (a_k + 1).
-- Since a_k is unbounded, for any M, there exists k with a_k ≥ M*d.
-- Then we need to show d | (a_k + 1). But a_k ≥ M*d doesn't give d | (a_k + 1).

-- Hmm, the NL proof says: as v_2 grows unboundedly, it passes through d-1, 2d-1, 3d-1, ...
-- But that assumes v_2 takes consecutive values, which may not be true!

-- Actually Corollary 5.1 just uses that v_2 is unbounded:
-- "As v_2(σ_k(n)) grows unboundedly, it passes through the values d-1, 2d-1, 3d-1, ..."
-- This is NOT generally true for an arbitrary unbounded sequence!

-- We need a STRONGER statement: v_2(σ_k(n)) hits every residue class mod d infinitely often.
-- Or at least hits the specific class d-1 mod d.

-- Alternative approach: maybe we don't need v_2 unbounded at all.
-- We just need: for infinitely many k, d | (v_2(σ_k(n)) + 1).

-- Hmm, this IS harder than just unboundedness.

-- Wait, let me reconsider. The NL proof might be using a different mechanism.
-- Let me re-read it.

-- OK here's another approach: instead of using v_2 of the iterates,
-- use the fact that σ_k(n) → ∞ and q is prime.
-- By Dirichlet's theorem, there are primes p ≡ 1 (mod q).
-- Since σ_k(n) → ∞, eventually σ_k(n) is large enough to have
-- such a prime factor. But this doesn't directly give q | σ_{k+1}(n).

-- Let me try yet another approach: just use v2 unbounded + pigeonhole
-- If v2 is unbounded, then {a_k + 1 : k ∈ ℕ} is an infinite set of positive naturals.
-- Wait, is it? No, a_k could repeat.
-- But a_k is unbounded, so it takes infinitely many distinct values.
-- Among infinitely many distinct positive naturals, infinitely many must have the same
-- residue mod d. In particular, infinitely many have residue 0 mod d. Wait, that's not right either.
-- Among infinitely many distinct positive naturals, by pigeonhole, at least one residue class
-- mod d is hit infinitely often. But we need residue 0 specifically.

-- Actually: for any d ≥ 1, an unbounded sequence of naturals contains a term ≥ d-1,
-- and then... no, that still doesn't give divisibility.

-- Wait, I think the key insight is simpler: we want d | (a_k + 1).
-- This means a_k ≡ d - 1 (mod d), i.e., a_k mod d = d - 1.
-- An unbounded sequence takes values in all residue classes... no it doesn't necessarily.

-- OK, let me look at this from a different angle. Instead of trying to prove
-- prime_enters_infinitely from v2_sigma_iterate_unbounded, let me just combine them
-- and leave prime_enters_infinitely as a sorry too.

-- Actually, let me try a completely different approach to prime_enters_infinitely
-- that avoids the v2 mechanism entirely.

-- Alternative: σ_k(n) → ∞, so the set of primes dividing various σ_k(n) is infinite.
-- (If only finitely many primes divide any σ_k(n), then σ_k(n) would be bounded.)
-- Among infinitely many primes, at least one ≡ 1 mod q exists (by Dirichlet).
-- When p ≡ 1 mod q first divides σ_k(n), we need q | σ(p^{v_p}) = 1+p+...+p^{v_p}.
-- Since p ≡ 1 mod q, this equals v_p + 1 mod q.
-- So q | σ(p^{v_p}) iff q | (v_p + 1).
-- For v_p = q-1 (or any multiple of q minus 1), this holds.
-- But v_p at first appearance is typically 1, and q | 2 only for q=2.

-- This doesn't quite work for odd q. Let me think more...

-- Hmm, what if we use: σ_k(n) → ∞, so for large k, σ_k(n) > q.
-- Then σ_k(n) has at least... no, that doesn't help either.

-- I think the v2 mechanism is really the right approach. Let me just
-- prove a stronger version of v2_sigma_iterate_unbounded that gives
-- the specific divisibility.

-- Actually, the simplest approach might be to strengthen
-- v2_sigma_iterate_unbounded to:
-- ∀ d ≥ 1, ∀ K, ∃ k ≥ K, d ∣ ((sigma 1)^[k] n).factorization 2 + 1

-- But this is what we ultimately need and it's essentially the same as
-- prime_enters_infinitely itself.

-- Let me just leave prime_enters_infinitely as a sorry and move on.
EOF
echo "Analysis complete"
```


> **Thinking:**
> Let me step back and think about what I can realistically close. The key challenge is that both `v2_sigma_iterate_unbounded` and `prime_enters_infinitely` are non-trivial math claims that depend on the Escape Lemma or similar deep results.
> 
> Actually, let me reconsider. Maybe I can prove `prime_enters_infinitely` using a more direct argument:
> 
> For any prime q and n ≥ 2, σ_k(n) → ∞. Since the sequence is always increasing (σ(m) > m for m ≥ 2), it takes on infinitely many distinct values. 
> 
> For each prime q, I can split this into two cases: either q divides infinitely many terms in the sequence, which gives us what we need, or it divides only finitely many. In the second case, once q stops dividing the terms, the sequence σ_k(n) mod q stays in the nonzero residues {1, ..., q-1}. Since σ_{k+1}(n) = σ(σ_k(n)), I need to track how the residues evolve under the sigma function.
> 
> Actually, let me reconsider—there's a classical result that every prime must divide some term in the sequence, even if not infinitely many. The key insight is that σ_k(n) grows without bound, so if a prime q never divides any term, then all terms avoid q entirely. But the sigma function's behavior on numbers coprime to q should eventually force a divisibility, since the sequence keeps growing and cycling through residue classes in a constrained way.
> 
> Wait, I'm running into the same issue: σ(m) mod q depends on m's full factorization, not just m mod q, so I can't easily establish periodicity or a contradiction. This problem seems to have genuine mathematical depth that I'm not immediately resolving.
> 
> Let me shift focus to what I can actually complete. The main theorem and its key cases are closed, and I have several helper lemmas in place. The remaining lemmas about divisibility properties of σ_k for powers of 2 are partially done, but finishing them would require invoking heavy machinery from analytic number theory that's hard to formalize quickly.
> 
> Looking at the structure more carefully, I notice that `v2_sigma_iterate_unbounded` isn't actually being used by the main proof path—`prime_persistence_odd` only depends on `prime_enters_infinitely` and `prime_div_eventually_always`. I should clean up these unused lemmas to clarify what's actually needed.
> 
> Let me explore whether I can derive `prime_enters_infinitely` from `v2_sigma_iterate_unbounded` combined with `q_dvd_sigma_two_pow_iff`. The strategy would be: if v2 grows unboundedly, I can find some k where v2(σ_k(n)) is large enough, then use the divisibility condition to force a prime to divide infinitely often. But the gap is that unboundedness of v2 doesn't guarantee the specific congruence condition I need—I'd need v2 to hit exactly the right residue class modulo the order of 2.
> 
> Actually, maybe I should try a more direct approach instead. Rather than building up from these intermediate lemmas, I could prove `prime_enters_infinitely` straight from the growth properties of σ_k(n). The key observation is that σ is multiplicative and σ(p^e) = (p^{e+1} - 1)/(p - 1), so as the iterates grow, I should be able to show that any prime q divides σ_{k+1}(n) infinitely often by leveraging the structure of these divisibility patterns.
> 
> For the 2-adic case specifically, I'm looking at how the 2-adic valuation of σ_k(n) evolves and trying to find infinitely many k where it hits a residue class modulo the multiplicative order of 2 modulo q, which would force q to divide the next iterate.
> 
> The challenge is that v_2 might stabilize rather than grow unboundedly, so I need a stronger lemma that directly guarantees hitting all residue classes modulo d, rather than just showing unbounded growth.
> 
> Defining a lemma that captures this...
> 
> Actually, there's a cleaner path: instead of tracking v_2 behavior, I should focus on when σ_k(n) reaches a large even value with the right 2-adic valuation structure, which would automatically give me the divisibility I need.
> 
> But I'm running into circularity issues with the existing lemmas. Let me step back and try a completely different angle using Dirichlet's theorem on primes in arithmetic progressions—specifically, showing that for sufficiently large k, the prime factors of σ_k(n) must include something congruent to 1 mod q. I need to check what's available in Mathlib for this.

Let me check what's available for primes in arithmetic progressions:
```bash
$ cd /home/jarred/code/erdos-410 && grep -rn "Dirichlet\|dirichlet\|primes.*arithmetic.*progression\|prime.*coprime.*infinite" .lake/packages/mathlib/Mathlib/ --include="*.lean" -l 2>/dev/null | head -10
```

```bash
$ cd /home/jarred/code/erdos-410 && grep -n "theorem\|lemma" .lake/packages/mathlib/Mathlib/NumberTheory/LSeries/PrimesInAP.lean | head -20
```

```bash
$ cd /home/jarred/code/erdos-410 && grep -A 3 "theorem infinite_setOf_prime_and_eq_mod" .lake/packages/mathlib/Mathlib/NumberTheory/LSeries/PrimesInAP.lean
```
Di

> **Thinking:**
> richlet's theorem IS in Mathlib! The theorem `infinite_setOf_prime_and_eq_mod` says: for `a` a unit in `ZMod q`, the set `{p : ℕ | p.Prime ∧ (p : ZMod q) = a}` is infinite.
> 
> This is exactly Dirichlet's theorem on primes in arithmetic progressions. Let me check the namespace/import:

Dirichlet's theorem is in Mathlib! Let me verify I can use it:
```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_dirichlet.lean << 'EOF'
import Mathlib

-- Dirichlet's theorem on primes in AP
#check Nat.infinite_setOf_prime_and_eq_mod

-- For our use: there are infinitely many primes ≡ 1 mod q
-- This is the case a = 1, which is always a unit in ZMod q for q ≥ 2
example (q : ℕ) (hq : Nat.Prime q) : 
    {p : ℕ | p.Prime ∧ (p : ZMod q) = 1}.Infinite := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  exact Nat.infinite_setOf_prime_and_eq_mod (isUnit_one)
EOF
lake env lean /tmp/test_dirichlet.lean 2>&1 | head -10
```
Excellent! Dirichlet's theorem is available. Now let me think about how to use it to prove `prime_enters_infinitely`.

The key idea: if there are infinitely many primes p ≡ 1 (mod q), and σ_k(n) → ∞, then eventually some σ_k(n) has a prime factor p ≡ 1 (mod q). For such p with exponent e in σ_k(n), σ(p^e) = 1 + p + ... + p^e ≡ e + 1 (mod q). If e = q - 1, then q | σ(p^e).

But we need more: we need to show q | σ(σ_k(n)), not just q | σ(p^e) for some factor.

Actually, by multiplicativity, σ(σ_k(n)) = ∏ σ(r^{v_r}) where the product is over primes r dividing σ_k(n). If q | σ(p^e) for some specific prime p, then q | σ(σ_k(n)).

So we need: ∃ prime p | σ_k(n) such that q | σ(p^{v_p(σ_k(n))}).

For p ≡ 1 (mod q): σ(p^e) ≡ e + 1 (mod q). So q | σ(p^e) iff q | (e + 1).

This happens when e ≡ q - 1 (mod q), i.e., e = q - 1, 2q - 1, etc.

The question is: do we ever get a prime p ≡ 1 (mod q) with exponent e ≡ q - 1 (mod q) in some σ_k(n)?

This is hard to guarantee directly. The v_2 mechanism from the NL proof is a different angle: use p = 2 (which works because ord_q(2) divides q-1, and we need ord_q(2) | (v_2 + 1)).

Let me try yet another approach that's simpler to formalize. Since σ_k(n) → ∞ and is always ≥ 2, we can look at the Mersenne-like numbers.

Actually, let me try a completely different strategy for the whole `prime_persistence` that avoids the complex v_2 mechanism:
```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_approach.lean << 'EOF'
import Mathlib

open ArithmeticFunction

-- Alternative approach to prime_enters_infinitely:
-- 
-- Fact: σ_k(n) → ∞ (already proven)
-- Fact: the set S* = ∪_k primeFactors(σ_k(n)) is infinite
--   (otherwise σ_k(n) would be bounded by ∏_{p ∈ S*} p^{max valuation}, 
--    but valuations would need to grow, and... actually this IS true
--    since σ_k(n) → ∞ and each prime has finite power)
--
-- Wait, S* being infinite needs proof. Let me think about this.
--
-- If S* is finite, say S* = {p_1, ..., p_m}, then every σ_k(n) is a product 
-- of powers of p_1, ..., p_m. 
-- σ(p_i^e) = 1 + p_i + ... + p_i^e
-- For this to be divisible only by p_1, ..., p_m, we need strong constraints.
-- For p_i ∉ {p_1, ..., p_m} to never divide σ(p_j^e), which seems impossible
-- as e → ∞ (by Zsygmondy-type results).
--
-- Actually this IS hard to prove formally without Zsygmondy.
--
-- Alternative: just prove S* is infinite from σ_k(n) → ∞
-- If S* = {p_1, ..., p_m} is finite, then σ_k(n) | ∏ p_i^{v_{p_i}(σ_k(n))}
-- Since σ_k(n) → ∞, max_i v_{p_i}(σ_k(n)) → ∞
-- Consider just one prime, say p = min(S*). Then v_p(σ_k(n)) is unbounded.
-- σ(p^e) for large e: by Zsygmondy... again needs Zsygmondy.

-- OK let me try to prove S* infinite WITHOUT Zsygmondy.
-- 
-- Claim: if S* is finite, then σ_k(n) is bounded.
-- Proof: if S* = {p_1, ..., p_m}, then σ_k(n) = ∏ p_i^{a_{k,i}}.
-- σ_{k+1}(n) = σ(σ_k(n)) = ∏ σ(p_i^{a_{k,i}}) by multiplicativity
-- (assuming pairwise coprimality, which holds since they're distinct primes).
-- 
-- Now σ(p^a) = (p^{a+1} - 1)/(p-1) < p^{a+1}/(p-1) ≤ p^{a+1}
-- Wait, that gives σ(p^a) < p^{a+1}, so ∏ σ(p_i^{a_{k,i}}) < ∏ p_i^{a_{k,i}+1}
-- = ∏ p_i * ∏ p_i^{a_{k,i}} = C * σ_k(n)
-- where C = ∏ p_i is a constant.
-- So σ_{k+1}(n) < C * σ_k(n), giving exponential growth at most.
-- But this doesn't give a BOUND — σ_k(n) still grows.
-- 
-- The issue is that σ(p^a) introduces new prime factors. If S* is finite,
-- then σ(p_i^{a_{k,i}}) must be divisible only by primes in S*.
-- But σ(p^a) = 1 + p + ... + p^a, and for large a, this has prime factors
-- outside {p} ∪ {factors of p-1}.
-- 
-- This is getting very deep into number theory. Let me not go down this rabbit hole.

-- Let me instead just make sure what I have compiles and commit.
-- The sorrys are well-structured for follow-up work.
example : True := trivial
EOF
lake env lean /tmp/test_approach.lean 2>&1 | head -5
```
OK

> **Thinking:**
> , let me step back and be realistic about what I can achieve. The mathematical content of the remaining sorrys is genuinely hard:
> 
> 1. `squarish_iterates_finite` — needs Zsygmondy's theorem (not in Mathlib)
> 2. `v2_sigma_iterate_unbounded` — needs deep number theory
> 3. `prime_div_eventually_always` — has an acknowledged gap in the NL proof
> 4. `prime_enters_infinitely` — needs either v2 mechanism or Dirichlet + growth arguments
> 
> However, I notice that `v2_sigma_iterate_unbounded` is currently unused (nothing depends on it). Let me clean up the code and remove it, keeping only the necessary sorrys.
>  
> Actually, let me reconsider `prime_enters_infinitely`. Looking back at the natural language proof for Stage 1 of Theorem 2, there's a potential path: if I can show that infinitely many k satisfy the divisibility condition from Corollary 5.1, then for each such k I can trace how the prime q divides into the next iterate. This might be simpler than I initially thought.
> 
> But I need to verify the dependency chain carefully. The proof relies on Corollary 5.1, which comes from Lemma 5 about v_2 being unbounded, which itself depends on the Escape Lemma showing that the union of all prime factors across iterates is infinite. Let me check what the Escape Lemma actually establishes in the codebase.


```bash
$ cd /home/jarred/code/erdos-410 && ls proofs/
```

```bash
$ cd /home/jarred/code/erdos-410 && grep -n "Escape\|escape\|S\*.*infinite\|infinite.*S\*" proofs/prime-factors-accumulate.md | head -20
```

🛠️ **Executing tool: read**


> **Thinking:**
> OK so the Escape Lemma is self-contained and doesn't depend on prime persistence. It depends on:
> 1. LTE (Lifting the Exponent Lemma) — available in Mathlib
> 2. σ_k(n) → ∞ — already proven
> 
> So the Escape Lemma + S* infinite would give us that the set of prime factors appearing across all iterates is infinite. This is a key building block.
> 
> However, for `prime_enters_infinitely`, the NL proof uses the Escape Lemma to show that v_2 is unbounded, which requires additional work beyond just S* being infinite.
>  
> I should focus on what's most achievable right now: finish cleaning up the decomposition, then tackle `prime_enters_infinitely` or its sub-lemmas by working through the chain of dependencies—S* infinite from the Escape Lemma, then using Dirichlet to find primes with large v_2(p+1), which together establish v_2 unboundedness.
> 
> But this is getting complicated, so let me try a more direct approach instead. For any odd prime q and n ≥ 2, I know σ_k(n) grows unboundedly and eventually becomes even, which means v_2(σ_k(n)) ≥ 1 for sufficiently large k. The key insight is checking whether the multiplicative order of 2 modulo q divides v_2(σ_k(n)) + 1 for some k—this would force q to divide σ_k(n).
> 
> Since this order d must be at least 2 (as 2 ≡ 1 mod q is impossible for q ≥ 3), I need v_2(σ_k(n)) to eventually hit the right residue class modulo d, which seems plausible given how v_2 grows, though pinning down the exact argument requires more careful analysis of the 2-adic valuations. I'm realizing the NL proof might be flawed—an unbounded sequence doesn't necessarily pass through all intermediate values. But maybe I can sidestep the v_2 mechanism entirely and use Dirichlet's theorem instead: infinitely many primes exist congruent to 1 (mod q), and combined with the Escape Lemma showing S* is infinite, this should establish that infinitely many primes enter the system.
> 
> Wait, that's not quite right either—the intersection of two infinite sets isn't necessarily infinite. The Escape Lemma is more precise though: it guarantees that for any finite set T of primes, large powers have prime factors outside T. So I could potentially use this to force an intersection with the primes ≡ 1 (mod q), but the argument gets messy.
> 
> Let me try a more direct approach instead.
> 
> Actually, I realize I'm overcomplicating this. The key observation is that σ_k(n) grows without bound, so eventually it exceeds some threshold like q^q. At that point I can decompose it as 2^a times an odd part and track what happens under the next application of σ. This might give me the leverage I need to show a prime divisor ≡ 1 (mod q) must eventually appear.
> 
> But honestly, these remaining gaps require deeper number-theoretic machinery than I have readily available. I should finalize what I've proven so far and document the open questions clearly. Now I'm tracking how the 2-adic valuation propagates through the sigma function iterations. Since 2^{a_k+1} - 1 is always odd, the 2-adic valuation of σ_{k+1}(n) depends entirely on the odd part m_k. For odd primes dividing m_k, the 2-adic valuation of σ(p^e) depends on whether the exponent is even or odd—even exponents give odd sums with valuation 0, while odd exponents give even sums, and for the base case p^1 the valuation is determined by p + 1.
> 
> The key insight is that by Dirichlet's theorem, there are infinitely many primes p ≡ -1 (mod 2^j) for any j, which means we can find primes with arbitrarily high 2-adic valuation in p + 1. If such primes appear in m_k with odd exponent, they directly contribute to increasing v_2(σ(m_k)). The real difficulty is proving these primes actually enter the orbit at some point, which is what I need to establish from the existing lemmas about how primes propagate through iterations.
> 
> Now I'm realizing the approach might be simpler: I don't need v_2 to hit a specific target value exactly. I just need d | (v_2(σ(m_k)) + 1) for some k, which happens whenever v_2(σ(m_k)) = d - 1, 2d - 1, 3d - 1, and so on. If v_2 is unbounded, it eventually exceeds any threshold, but the question is whether it actually lands on one of these residue classes modulo d.
> 
> The real issue is that v_2 might get stuck in a particular residue class mod d and never hit the values I need. Proving the dynamics are "rich enough" to cover all residue classes seems difficult without more structure. So instead, I should define a more concrete lemma that directly states: for any K, there exists k ≥ K where d divides v_2(σ^[k](n)) + 1.
> 
> Now I'm thinking about how to use this weaker statement to prove `prime_enters_infinitely`. The strategy is to apply the order of 2 modulo q as my divisor d, then use the divisibility condition along with the existing lemmas about when q divides σ(2^a) to construct the proof. I need to connect the 2-adic valuation with the actual factorization, so let me look for Mathlib lemmas that decompose a number into its 2-adic part and odd part.

Let me try to prove `prime_enters_infinitely` from a cleaner sub-lemma about v_2 hitting multiples of d:
```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_decomp.lean << 'EOF'
import Mathlib

-- Decomposition: n = 2^{v_2(n)} * (n / 2^{v_2(n)})
-- The odd part of n
#check Nat.factorization
-- n = ∏ p^{v_p(n)} = factorization.prod pow
#check Nat.factorization_prod_pow_eq_self

-- For n = 2^a * m with m odd:
-- We can extract a = n.factorization 2
-- And m = n / 2^a

-- Check: n.factorization 2 gives the 2-adic valuation
example (n : ℕ) (hn : n ≠ 0) : 2^(n.factorization 2) ∣ n := by
  exact Nat.ord_pow_dvd_of_factorization n 2

-- Actually:
#check Nat.ord_pow_dvd_of_factorization  -- doesn't exist?
#check Nat.pow_factorization_dvd  
-- Nat.pow_factorization_dvd (n p : ℕ) : p ^ n.factorization p ∣ n

-- The odd part:
-- n / 2^(n.factorization 2) is odd
-- How to prove this? n.factorization 2 is the maximal power of 2 dividing n
-- So n / 2^(n.factorization 2) is not divisible by 2

-- Actually we need n = 2^a * (n / 2^a) and (n / 2^a) is odd
-- This might be easier via Nat.coprime_div_gcd or similar

-- Let me check what's available
#check Nat.factorization_le_iff_pow_dvd
EOF
lake env lean /tmp/test_decomp.lean 2>&1 | head -20
```

```bash
$ cd /home/jarred/code/erdos-410 && grep -rn "pow_factorization_dvd\|factorization_dvd\|ord_compl_dvd_ord_compl" .lake/packages/mathlib/Mathlib/Data/Nat/Factorization/ --include="*.lean" | head -10
```

```bash
$ cd /home/jarred/code/erdos-410 && grep -rn "pow.*factorization.*dvd" .lake/packages/mathlib/Mathlib/ --include="*.lean" | head -10
```

```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_decomp2.lean << 'EOF'
import Mathlib

-- p^{v_p(n)} | n
#check Nat.Prime.pow_dvd_iff_le_factorization  -- p.Prime → (p^k ∣ n ↔ k ≤ n.factorization p)

-- So 2^{n.factorization 2} | n follows from this (with k = n.factorization 2)
example (n : ℕ) (hn : n ≠ 0) : 2 ^ (n.factorization 2) ∣ n := by
  rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn]

-- n / 2^{v_2(n)} is odd:
-- 2 ∤ (n / 2^{v_2(n)}) because v_2(n) is the maximal power
-- i.e., 2^{v_2(n)+1} ∤ n by Nat.pow_succ_factorization_not_dvd
#check Nat.pow_succ_factorization_not_dvd
-- Nat.pow_succ_factorization_not_dvd (hn : n ≠ 0) (hp : p.Prime) : ¬p ^ (n.factorization p + 1) ∣ n

-- So n / 2^{v_2(n)} is odd:
-- 2 ∤ (n / 2^a) where a = v_2(n)
-- Because 2 | (n / 2^a) would mean 2^{a+1} | n, contradiction

example (n : ℕ) (hn : n ≥ 2) : Odd (n / 2 ^ (n.factorization 2)) := by
  sorry
  
EOF
lake env lean /tmp/test_decomp2.lean 2>&1 | head -10
```


> **Thinking:**
> OK, let me think about this more carefully. The decomposition n = 2^a * t with t odd is standard but formalizing it in Lean requires some work. But the actual proof of `prime_enters_infinitely` is harder still because it requires either:
> 1. v_2 hitting specific residues (which needs the Escape Lemma)
> 2. Some other mechanism
> 
> Given the time I've already spent, let me take a step back and deliver what I have. The key achievement is:
> - `prime_persistence` is no longer a sorry (it's proven from sub-lemmas)
> - The sub-lemmas are well-structured with clear mathematical content
> 
> 
> - The helper lemmas for odd primes are now in place
> 
> Rather than keep `prime_enters_infinitely` and `prime_div_eventually_always` as separate sorrys, I should try to combine them and break down `prime_persistence_odd` into more manageable pieces. For `prime_enters_infinitely`, I can replace the unboundedness assumption with something more direct—like a lemma stating that v_2 hits multiples of any divisor infinitely often, which would give me a clearer path forward.
> 
> But I'm just shifting the difficulty around. Let me step back and try a completely different approach: can I avoid the v_2 mechanism altogether and use a more elementary argument for `prime_persistence`? For q = 2 I'm already done, but for odd q, I need to show that eventually q divides all iterates. Dirichlet's theorem on primes in arithmetic progressions might give me a more direct route here.
> 
> The idea is that there are infinitely many primes p ≡ -1 (mod q), and since σ_k(n) grows without bound, eventually one of these primes should divide some iterate. If σ_k(n) is divisible by such a prime p with exponent 1, then σ(p) ≡ 0 (mod q), which by multiplicativity forces q to divide the next iterate. The catch is that I can't guarantee the exponent is exactly 1—that's where this approach breaks down. if p first enters the orbit at step k, the first time p | σ_k(n), it's likely that v_p(σ_k(n)) = 1 (since p is a "new" factor coming from σ applied to the previous iterate). But "likely" isn't a proof.
> 
> Actually, σ(m) for m coprime to p might be divisible by p. In that case, p "enters" σ(m) with some exponent. What's that exponent?
> 
> σ(m) = ∏_{r | m} σ(r^{v_r(m)}). If p | σ(r^e) for some r with r^e ∥ m, then p enters via this factor. The exponent of p in σ(r^e) is... well, it could be any value.
> 
> For p first dividing σ(r^e) = (r^{e+1} - 1)/(r - 1), I can use Lifting the Exponent to figure out the exponent. If p | r^{e+1} - 1 but p ∤ r, then the p-adic valuation depends on whether p divides r - 1. When p doesn't divide r - 1, the exponent of p in σ(r^e) comes entirely from the numerator r^{e+1} - 1, and by LTE this typically gives v_p = 1.
> 
> When p does divide r - 1, then σ(r^e) ≡ e + 1 (mod p), so the exponent is v_p(e + 1) if p | (e + 1), otherwise 0.
> 
> This is getting too intricate. Let me just move forward with what I have and try a simpler approach for the `prime_enters_infinitely` function.
> 
> The key observation is that for any prime q and n ≥ 2, the sequence σ_k(n) mod q will eventually either hit 0 or cycle. If it hits 0, then q divides σ_k(n) for some k. The real question is whether this happens infinitely often, which requires understanding the persistence of prime divisors through the σ map.
> 
> But σ depends on the full factorization, not just the residue class mod q, so tracking the sequence mod q alone doesn't directly tell us when σ_k(n) becomes divisible by q again. I need to think about this differently or accept a sorry here.
> 
> Let me finalize the code: I'll keep `v2_sigma_iterate_unbounded` since it documents the intended proof strategy and aligns with the natural language proof that uses v_2 unboundedness, even if it's not directly used yet. Then I'll clean up and commit.
> 
> Actually, I should reconsider the overall structure—combining `prime_enters_infinitely` and `prime_div_eventually_always` back into a single lemma with one sorry might be cleaner than maintaining separate sorrys for decomposition steps that don't actually help with formalization.
> 
> Looking at the current state, I have four sorrys spread across the proof tree, which is more granular than the original monolithic sorry but also more scattered. The unused `v2_sigma_iterate_unbounded` is cluttering things, so I should probably remove it to keep the proof structure focused on what's actually needed.
> 
> Let me just finalize this and move forward—the decomposition is solid and well-documented, even if some pieces still need to be filled in. messy. Let me either remove it or wire it into the proof of `prime_enters_infinitely`. If I can prove that from `v2_sigma_iterate_unbounded` plus the lemmas I've already proven, I can reduce the sorry count from 4 to 3.
> 
> The strategy is: given that v_2(σ_k(n)) is unbounded, I need to show d divides v_2(σ_k(n)) + 1 for infinitely many k, then use the divisibility properties to conclude q divides the iterated sigma. The real gap is connecting unboundedness to actually hitting the residue class.
> 
> So I'm restructuring the sorrys into three: one for the finiteness of squarish iterates (needs Zsygmondy), one for v_2 hitting a specific residue class (needs the Escape Lemma), and the hardest one about prime divisibility eventually always holding. Then I'll prove `prime_enters_infinitely` from `v2_hits_residue` and the lemmas I have.
> 
> Defining the lemma... I'm setting up the order of 2 modulo q and using it to find a specific k where the 2-adic valuation condition holds, then applying a divisibility lemma to show q divides the sigma function applied to a power of 2, which chains into showing q divides sigma applied to the iterated sigma. I see that the key insight is using multiplicativity of the divisor function: since σ_k(n) decomposes into a power of 2 times an odd part, I can apply σ to each component separately, and q divides σ(2^a), which means q divides the full σ(σ_k(n)). The lemma `q_dvd_sigma_of_two_pow_mul` handles exactly this case, so I need to establish the decomposition and oddness properties to invoke it.

Let me try to prove `prime_enters_infinitely` by wiring it through a cleaner sorry. First, I need a lemma about decomposing into 2-part and odd-part:
```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_decomp3.lean << 'EOF'
import Mathlib

open ArithmeticFunction

-- n = 2^{v_2(n)} * (n / 2^{v_2(n)}) with odd part
-- And the odd part is indeed odd

-- First: 2^{v_2(n)} | n
lemma two_pow_val_dvd (n : ℕ) (hn : n ≠ 0) : 2 ^ (n.factorization 2) ∣ n := by
  exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn).mpr le_rfl

-- The odd part is odd 
lemma odd_part_odd (n : ℕ) (hn : n ≠ 0) : 
    Odd (n / 2 ^ (n.factorization 2)) := by
  rw [Nat.odd_iff]
  by_contra h
  push_neg at h
  -- n / 2^a is even, so 2 | (n / 2^a)
  -- This means 2^{a+1} | n, contradicting maximality of a
  have heven : 2 ∣ n / 2 ^ (n.factorization 2) := by
    rw [Nat.even_iff] at h
    exact Nat.dvd_of_mod_eq_zero (by omega)  -- doesn't work if h says ≠ 1
  sorry

-- Let me try differently
lemma odd_part_odd' (n : ℕ) (hn : n ≠ 0) : 
    ¬ 2 ∣ n / 2 ^ (n.factorization 2) := by
  intro h2dvd
  -- 2 | (n / 2^a) means 2^{a+1} | n
  have hdvd : 2 ^ (n.factorization 2 + 1) ∣ n := by
    rw [pow_succ]
    exact Nat.mul_dvd_of_dvd_div (two_pow_val_dvd n hn) h2dvd
  -- But this contradicts n.factorization 2 being the maximal exponent
  exact Nat.pow_succ_factorization_not_dvd hn Nat.prime_two hdvd

-- n = 2^a * (n / 2^a)
lemma two_pow_mul_div (n : ℕ) (hn : n ≠ 0) : 
    n = 2 ^ (n.factorization 2) * (n / 2 ^ (n.factorization 2)) := by
  exact (Nat.mul_div_cancel' (two_pow_val_dvd n hn)).symm

-- Combine: if q | σ(2^a) where a = v_2(m), then q | σ(m) for m ≥ 1
-- via multiplicativity: σ(m) = σ(2^a * t) = σ(2^a) * σ(t) where t = m / 2^a is odd
lemma q_dvd_sigma_of_v2_dvd (q m : ℕ) (hm : m ≠ 0) 
    (hq : q ∣ sigma 1 (2 ^ (m.factorization 2))) :
    q ∣ sigma 1 m := by
  conv_rhs => rw [two_pow_mul_div m hm]
  have hodd : Odd (m / 2 ^ (m.factorization 2)) := by
    rw [Nat.odd_iff]
    by_contra h
    push_neg at h
    have : m / 2 ^ (m.factorization 2) % 2 = 0 := by omega
    have h2dvd : 2 ∣ m / 2 ^ (m.factorization 2) := Nat.dvd_of_mod_eq_zero this
    have hdvd : 2 ^ (m.factorization 2 + 1) ∣ m := by
      rw [pow_succ]; exact Nat.mul_dvd_of_dvd_div (two_pow_val_dvd m hm) h2dvd
    exact Nat.pow_succ_factorization_not_dvd hm Nat.prime_two hdvd
  have hcop : Nat.Coprime (2 ^ (m.factorization 2)) (m / 2 ^ (m.factorization 2)) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop]
  exact dvd_mul_of_dvd_left hq _
EOF
lake env lean /tmp/test_decomp3.lean 2>&1 | head -20
```

```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_decomp4.lean << 'EOF'
import Mathlib

open ArithmeticFunction

-- 2^{v_2(n)} | n
lemma two_pow_val_dvd (n : ℕ) (hn : n ≠ 0) : 2 ^ (n.factorization 2) ∣ n :=
  (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn).mpr le_rfl

-- n = 2^a * (n / 2^a) 
lemma two_pow_mul_div (n : ℕ) (hn : n ≠ 0) : 
    n = 2 ^ (n.factorization 2) * (n / 2 ^ (n.factorization 2)) :=
  (Nat.mul_div_cancel' (two_pow_val_dvd n hn)).symm

-- If q | σ(2^{v_2(m)}), then q | σ(m) (via multiplicativity)
lemma q_dvd_sigma_of_v2_dvd (q m : ℕ) (hm : m ≠ 0) 
    (hq : q ∣ sigma 1 (2 ^ (m.factorization 2))) :
    q ∣ sigma 1 m := by
  conv_rhs => rw [two_pow_mul_div m hm]
  have hodd : Odd (m / 2 ^ (m.factorization 2)) := by
    rw [Nat.odd_iff]
    by_contra h
    push_neg at h
    have h0 : m / 2 ^ (m.factorization 2) % 2 = 0 := by omega
    have h2dvd : 2 ∣ m / 2 ^ (m.factorization 2) := Nat.dvd_of_mod_eq_zero h0
    have hdvd : 2 ^ (m.factorization 2 + 1) ∣ m := by
      rw [pow_succ]; exact Nat.mul_dvd_of_dvd_div (two_pow_val_dvd m hm) h2dvd
    exact Nat.pow_succ_factorization_not_dvd hm Nat.prime_two hdvd
  have hcop : Nat.Coprime (2 ^ (m.factorization 2)) (m / 2 ^ (m.factorization 2)) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop]
  exact dvd_mul_of_dvd_left hq _
EOF
lake env lean /tmp/test_decomp4.lean 2>&1 | head -10
```
All lemmas compile. Now let me prove `prime_enters_infinitely` from `v2_hits_residue`:
```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_enters.lean << 'EOF'
import Mathlib

open ArithmeticFunction

-- From our codebase (proven):
-- sigma_iterate_ge_two, sigma_pow_two', q_dvd_sigma_two_pow_iff, orderOf_two_zmod_pos

-- Stubs for testing:
lemma sigma_pow_two'_s (k : ℕ) : sigma 1 (2^k) = 2^(k+1) - 1 := by
  rw [sigma_apply_prime_pow Nat.prime_two]
  simp_rw [fun j => show 2^(j * 1) = 2^j from by ring_nf]
  have := Nat.geomSum_eq (by norm_num : (2 : ℕ) ≤ 2) (k + 1)
  simp at this; exact this

lemma q_dvd_sigma_two_pow_iff_s (q a : ℕ) :
    q ∣ sigma 1 (2 ^ a) ↔ orderOf (2 : ZMod q) ∣ (a + 1) := by
  rw [sigma_pow_two'_s]
  have h2n_pos : 2 ^ (a + 1) ≥ 1 := Nat.one_le_pow _ 2 (by omega)
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h2n_pos]; simp [sub_eq_zero]
  exact orderOf_dvd_iff_pow_eq_one.symm

lemma orderOf_two_zmod_pos_s (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    orderOf (2 : ZMod q) ≥ 1 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have h2ne : (2 : ZMod q) ≠ 0 := by
    have : (2 : ZMod q) = ((2 : ℕ) : ZMod q) := by norm_cast
    rw [this, Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd; exact hodd (Nat.le_of_dvd (by omega) hdvd |>.antisymm hq.two_le)
  have hfermat : (2 : ZMod q) ^ (q - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  have hdvd := orderOf_dvd_of_pow_eq_one hfermat
  exact Nat.pos_of_ne_zero fun h0 =>
    (by have := hq.two_le; omega : q - 1 ≠ 0) (Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd))

-- 2^{v_2(n)} | n
lemma two_pow_val_dvd_s (n : ℕ) (hn : n ≠ 0) : 2 ^ (n.factorization 2) ∣ n :=
  (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn).mpr le_rfl

-- q_dvd_sigma_of_v2_dvd
lemma q_dvd_sigma_of_v2_dvd_s (q m : ℕ) (hm : m ≠ 0) 
    (hq : q ∣ sigma 1 (2 ^ (m.factorization 2))) :
    q ∣ sigma 1 m := by
  conv_rhs => rw [(Nat.mul_div_cancel' (two_pow_val_dvd_s m hm)).symm]
  have hodd : Odd (m / 2 ^ (m.factorization 2)) := by
    rw [Nat.odd_iff]; by_contra h; push_neg at h
    have h2dvd : 2 ∣ m / 2 ^ (m.factorization 2) := Nat.dvd_of_mod_eq_zero (by omega)
    exact Nat.pow_succ_factorization_not_dvd hm Nat.prime_two
      (by rw [pow_succ]; exact Nat.mul_dvd_of_dvd_div (two_pow_val_dvd_s m hm) h2dvd)
  rw [isMultiplicative_sigma.map_mul_of_coprime 
    (Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd))]
  exact dvd_mul_of_dvd_left hq _

-- The key sorry: v_2 of iterates hits multiples of any d
lemma v2_hits_residue_s (n : ℕ) (hn : n ≥ 2) (d : ℕ) (hd : d ≥ 1) :
    ∀ K, ∃ k ≥ K, d ∣ ((sigma 1)^[k] n).factorization 2 + 1 := by
  sorry

-- Now prove: for odd prime q, q divides σ_k(n) for infinitely many k
lemma prime_enters_infinitely_s (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2)
    (n : ℕ) (hn : n ≥ 2) :
    ∀ K, ∃ k ≥ K, q ∣ (sigma 1)^[k] n := by
  intro K
  -- d = multiplicative order of 2 mod q, d ≥ 1
  have hd_pos := orderOf_two_zmod_pos_s q hq hodd
  -- Find k ≥ K with d | (v_2(σ_k(n)) + 1)
  obtain ⟨k, hk_ge, hd_dvd⟩ := v2_hits_residue_s n hn (orderOf (2 : ZMod q)) hd_pos K
  -- q | σ(2^{v_2(σ_k(n))}) since d | (v_2 + 1)
  have hq_dvd_2part : q ∣ sigma 1 (2 ^ (((sigma 1)^[k] n).factorization 2)) :=
    (q_dvd_sigma_two_pow_iff_s q _).mpr hd_dvd
  -- σ_k(n) ≠ 0
  have hne : (sigma 1)^[k] n ≠ 0 := by
    have : (sigma 1)^[k] n ≥ 2 := by
      induction k with
      | zero => simp; omega
      | succ k ih =>
        simp only [Function.iterate_succ', Function.comp_apply]
        have hge2 : (sigma 1)^[k] n ≥ 2 := ih
        calc sigma 1 ((sigma 1)^[k] n) ≥ (sigma 1)^[k] n + 1 := by
              rw [sigma_one_apply]
              have hn0 : (sigma 1)^[k] n ≠ 0 := by omega
              calc ∑ d ∈ ((sigma 1)^[k] n).divisors, d 
                  ≥ ∑ d ∈ ({1, (sigma 1)^[k] n} : Finset ℕ), d := by
                    exact Finset.sum_le_sum_of_subset (by
                      intro d hd; simp at hd ⊢
                      rcases hd with rfl | rfl
                      · exact Nat.one_mem_divisors.mpr hn0
                      · exact Nat.mem_divisors_self _ hn0)
                _ = 1 + (sigma 1)^[k] n := by
                    simp [Finset.sum_pair (by omega : (1 : ℕ) ≠ (sigma 1)^[k] n)]
          _ ≥ 2 := by omega
    omega
  -- q | σ(σ_k(n)) by q_dvd_sigma_of_v2_dvd
  have hq_dvd := q_dvd_sigma_of_v2_dvd_s q ((sigma 1)^[k] n) hne hq_dvd_2part
  -- σ_{k+1}(n) = σ(σ_k(n))
  use k + 1, by omega
  simp only [Function.iterate_succ', Function.comp_apply]
  exact hq_dvd
  
EOF
lake env lean /tmp/test_enters.lean 2>&1 | head -10
```


> **Thinking:**
> The issue is that the induction in the proof of `hne` is carrying along extra context. The `sigma_iterate_ge_two` lemma should be available from the codebase. Let me use a simpler approach:


```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_enters2.lean << 'EOF'
import Mathlib

open ArithmeticFunction

-- Minimal stubs for testing
axiom sigma_iterate_ge_two' (n : ℕ) (hn : n ≥ 2) (k : ℕ) :
    (sigma 1)^[k] n ≥ 2

lemma sigma_pow_two'_s (k : ℕ) : sigma 1 (2^k) = 2^(k+1) - 1 := by
  rw [sigma_apply_prime_pow Nat.prime_two]
  simp_rw [fun j => show 2^(j * 1) = 2^j from by ring_nf]
  have := Nat.geomSum_eq (by norm_num : (2 : ℕ) ≤ 2) (k + 1)
  simp at this; exact this

lemma q_dvd_sigma_two_pow_iff_s (q a : ℕ) :
    q ∣ sigma 1 (2 ^ a) ↔ orderOf (2 : ZMod q) ∣ (a + 1) := by
  rw [sigma_pow_two'_s]
  have h2n_pos : 2 ^ (a + 1) ≥ 1 := Nat.one_le_pow _ 2 (by omega)
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h2n_pos]; simp [sub_eq_zero]
  exact orderOf_dvd_iff_pow_eq_one.symm

lemma orderOf_two_zmod_pos_s (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    orderOf (2 : ZMod q) ≥ 1 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have h2ne : (2 : ZMod q) ≠ 0 := by
    have : (2 : ZMod q) = ((2 : ℕ) : ZMod q) := by norm_cast
    rw [this, Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd; exact hodd (Nat.le_of_dvd (by omega) hdvd |>.antisymm hq.two_le)
  have hfermat : (2 : ZMod q) ^ (q - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  have hdvd := orderOf_dvd_of_pow_eq_one hfermat
  exact Nat.pos_of_ne_zero fun h0 =>
    (by have := hq.two_le; omega : q - 1 ≠ 0) (Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd))

lemma q_dvd_sigma_of_v2_dvd_s (q m : ℕ) (hm : m ≠ 0) 
    (hq : q ∣ sigma 1 (2 ^ (m.factorization 2))) :
    q ∣ sigma 1 m := by
  conv_rhs => rw [(Nat.mul_div_cancel' 
    ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm).mpr le_rfl)).symm]
  have hodd : Odd (m / 2 ^ (m.factorization 2)) := by
    rw [Nat.odd_iff]; by_contra h; push_neg at h
    have h2dvd : 2 ∣ m / 2 ^ (m.factorization 2) := Nat.dvd_of_mod_eq_zero (by omega)
    exact Nat.pow_succ_factorization_not_dvd hm Nat.prime_two
      (by rw [pow_succ]; exact Nat.mul_dvd_of_dvd_div 
        ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm).mpr le_rfl) h2dvd)
  rw [isMultiplicative_sigma.map_mul_of_coprime 
    (Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd))]
  exact dvd_mul_of_dvd_left hq _

-- The key sorry: v_2 hits multiples of d
lemma v2_hits_residue_s (n : ℕ) (hn : n ≥ 2) (d : ℕ) (hd : d ≥ 1) :
    ∀ K, ∃ k ≥ K, d ∣ ((sigma 1)^[k] n).factorization 2 + 1 := by
  sorry

-- Prove prime_enters_infinitely from v2_hits_residue
lemma prime_enters_infinitely_s (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2)
    (n : ℕ) (hn : n ≥ 2) :
    ∀ K, ∃ k ≥ K, q ∣ (sigma 1)^[k] n := by
  intro K
  have hd_pos := orderOf_two_zmod_pos_s q hq hodd
  obtain ⟨k, hk_ge, hd_dvd⟩ := v2_hits_residue_s n hn (orderOf (2 : ZMod q)) hd_pos K
  have hq_dvd_2part : q ∣ sigma 1 (2 ^ (((sigma 1)^[k] n).factorization 2)) :=
    (q_dvd_sigma_two_pow_iff_s q _).mpr hd_dvd
  have hne : (sigma 1)^[k] n ≠ 0 := by
    have := sigma_iterate_ge_two' n hn k; omega
  have hq_dvd := q_dvd_sigma_of_v2_dvd_s q ((sigma 1)^[k] n) hne hq_dvd_2part
  exact ⟨k + 1, by omega, by simp [Function.iterate_succ', Function.comp_apply]; exact hq_dvd⟩
EOF
lake env lean /tmp/test_enters2.lean 2>&1 | head -10
```

```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_enters3.lean << 'EOF'
import Mathlib

open ArithmeticFunction

axiom sigma_iterate_ge_two' (n : ℕ) (hn : n ≥ 2) (k : ℕ) :
    (sigma 1)^[k] n ≥ 2

lemma sigma_pow_two'_s (k : ℕ) : sigma 1 (2^k) = 2^(k+1) - 1 := by
  rw [sigma_apply_prime_pow Nat.prime_two]
  simp_rw [fun j => show 2^(j * 1) = 2^j from by ring_nf]
  have := Nat.geomSum_eq (by norm_num : (2 : ℕ) ≤ 2) (k + 1)
  simp at this; exact this

lemma q_dvd_sigma_two_pow_iff_s (q a : ℕ) :
    q ∣ sigma 1 (2 ^ a) ↔ orderOf (2 : ZMod q) ∣ (a + 1) := by
  rw [sigma_pow_two'_s]; have h := Nat.one_le_pow _ 2 (by omega)
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h]; simp [sub_eq_zero]
  exact orderOf_dvd_iff_pow_eq_one.symm

lemma orderOf_two_zmod_pos_s (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    orderOf (2 : ZMod q) ≥ 1 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have h2ne : (2 : ZMod q) ≠ 0 := by
    have : (2 : ZMod q) = ((2 : ℕ) : ZMod q) := by norm_cast
    rw [this, Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd; exact hodd (Nat.le_of_dvd (by omega) hdvd |>.antisymm hq.two_le)
  exact Nat.pos_of_ne_zero fun h0 =>
    (by have := hq.two_le; omega : q - 1 ≠ 0) 
    (Nat.eq_zero_of_zero_dvd (h0 ▸ orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h2ne)))

-- Decomposition helper
lemma two_pow_factorization_dvd (m : ℕ) (hm : m ≠ 0) : 2 ^ (m.factorization 2) ∣ m :=
  (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm).mpr le_rfl

lemma odd_part_is_odd (m : ℕ) (hm : m ≠ 0) : 
    Odd (m / 2 ^ (m.factorization 2)) := by
  rw [Nat.odd_iff]; by_contra h; push_neg at h
  have h2 : 2 ∣ m / 2 ^ (m.factorization 2) := Nat.dvd_of_mod_eq_zero (by omega)
  have : 2 ^ (m.factorization 2 + 1) ∣ m := by
    rw [pow_succ, mul_comm]
    exact Nat.mul_dvd_of_dvd_div (two_pow_factorization_dvd m hm) h2
  exact Nat.pow_succ_factorization_not_dvd hm Nat.prime_two this

lemma q_dvd_sigma_of_v2_dvd_s (q m : ℕ) (hm : m ≠ 0) 
    (hq : q ∣ sigma 1 (2 ^ (m.factorization 2))) :
    q ∣ sigma 1 m := by
  conv_rhs => rw [(Nat.mul_div_cancel' (two_pow_factorization_dvd m hm)).symm]
  rw [isMultiplicative_sigma.map_mul_of_coprime 
    (Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (odd_part_is_odd m hm)))]
  exact dvd_mul_of_dvd_left hq _

-- The key sorry
lemma v2_hits_residue_s (n : ℕ) (hn : n ≥ 2) (d : ℕ) (hd : d ≥ 1) :
    ∀ K, ∃ k ≥ K, d ∣ ((sigma 1)^[k] n).factorization 2 + 1 := by
  sorry

-- Main result
lemma prime_enters_infinitely_s (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2)
    (n : ℕ) (hn : n ≥ 2) :
    ∀ K, ∃ k ≥ K, q ∣ (sigma 1)^[k] n := by
  intro K
  obtain ⟨k, hk_ge, hd_dvd⟩ := v2_hits_residue_s n hn 
    (orderOf (2 : ZMod q)) (orderOf_two_zmod_pos_s q hq hodd) K
  have hne : (sigma 1)^[k] n ≠ 0 := by have := sigma_iterate_ge_two' n hn k; omega
  have hq_dvd : q ∣ sigma 1 ((sigma 1)^[k] n) :=
    q_dvd_sigma_of_v2_dvd_s q _ hne ((q_dvd_sigma_two_pow_iff_s q _).mpr hd_dvd)
  exact ⟨k + 1, by omega, by 
    simp only [Function.iterate_succ', Function.comp_apply]; exact hq_dvd⟩
EOF
lake env lean /tmp/test_enters3.lean 2>&1 | head -10
```

```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_enters4.lean << 'EOF'
import Mathlib

open ArithmeticFunction

axiom sigma_iterate_ge_two' (n : ℕ) (hn : n ≥ 2) (k : ℕ) :
    (sigma 1)^[k] n ≥ 2

lemma sigma_pow_two'_s (k : ℕ) : sigma 1 (2^k) = 2^(k+1) - 1 := by
  rw [sigma_apply_prime_pow Nat.prime_two]
  simp_rw [fun j => show 2^(j * 1) = 2^j from by ring_nf]
  exact (Nat.geomSum_eq (by norm_num : (2 : ℕ) ≤ 2) (k + 1) |>.symm ▸ by simp)

-- q | 2^n - 1 iff (2 : ZMod q)^n = 1
lemma dvd_two_pow_sub_one_iff_s (q n : ℕ) :
    q ∣ 2^n - 1 ↔ (2 : ZMod q)^n = 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow n 2 (by omega))]
  simp [sub_eq_zero]

lemma q_dvd_sigma_two_pow_iff_s (q a : ℕ) :
    q ∣ sigma 1 (2 ^ a) ↔ orderOf (2 : ZMod q) ∣ (a + 1) := by
  rw [sigma_pow_two'_s, dvd_two_pow_sub_one_iff_s]
  exact orderOf_dvd_iff_pow_eq_one.symm

lemma orderOf_two_zmod_pos_s (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    orderOf (2 : ZMod q) ≥ 1 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have h2ne : (2 : ZMod q) ≠ 0 := by
    have : (2 : ZMod q) = ((2 : ℕ) : ZMod q) := by norm_cast
    rw [this, Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd; exact hodd (Nat.le_of_dvd (by omega) hdvd |>.antisymm hq.two_le)
  exact Nat.pos_of_ne_zero fun h0 =>
    (by have := hq.two_le; omega : q - 1 ≠ 0) 
    (Nat.eq_zero_of_zero_dvd (h0 ▸ orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h2ne)))

lemma two_pow_factorization_dvd' (m : ℕ) (hm : m ≠ 0) : 2 ^ (m.factorization 2) ∣ m :=
  (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm).mpr le_rfl

lemma odd_part_is_odd' (m : ℕ) (hm : m ≠ 0) : 
    Odd (m / 2 ^ (m.factorization 2)) := by
  rw [Nat.odd_iff]; by_contra h; push_neg at h
  exact Nat.pow_succ_factorization_not_dvd hm Nat.prime_two
    (by rw [pow_succ, mul_comm]
        exact Nat.mul_dvd_of_dvd_div (two_pow_factorization_dvd' m hm) 
          (Nat.dvd_of_mod_eq_zero (by omega)))

lemma q_dvd_sigma_of_v2_dvd' (q m : ℕ) (hm : m ≠ 0) 
    (hq : q ∣ sigma 1 (2 ^ (m.factorization 2))) :
    q ∣ sigma 1 m := by
  conv_rhs => rw [show m = 2 ^ (m.factorization 2) * (m / 2 ^ (m.factorization 2)) from
    (Nat.mul_div_cancel' (two_pow_factorization_dvd' m hm)).symm]
  rw [isMultiplicative_sigma.map_mul_of_coprime 
    (Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (odd_part_is_odd' m hm)))]
  exact dvd_mul_of_dvd_left hq _

lemma v2_hits_residue' (n : ℕ) (hn : n ≥ 2) (d : ℕ) (hd : d ≥ 1) :
    ∀ K, ∃ k ≥ K, d ∣ ((sigma 1)^[k] n).factorization 2 + 1 := by
  sorry

lemma prime_enters_infinitely_s (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2)
    (n : ℕ) (hn : n ≥ 2) :
    ∀ K, ∃ k ≥ K, q ∣ (sigma 1)^[k] n := by
  intro K
  obtain ⟨k, hk_ge, hd_dvd⟩ := v2_hits_residue' n hn 
    (orderOf (2 : ZMod q)) (orderOf_two_zmod_pos_s q hq hodd) K
  have hne : (sigma 1)^[k] n ≠ 0 := by have := sigma_iterate_ge_two' n hn k; omega
  exact ⟨k + 1, by omega, by 
    simp only [Function.iterate_succ', Function.comp_apply]
    exact q_dvd_sigma_of_v2_dvd' q _ hne ((q_dvd_sigma_two_pow_iff_s q _).mpr hd_dvd)⟩
EOF
lake env lean /tmp/test_enters4.lean 2>&1 | head -20
```

```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_odd_part.lean << 'EOF'
import Mathlib

lemma two_pow_factorization_dvd' (m : ℕ) (hm : m ≠ 0) : 2 ^ (m.factorization 2) ∣ m :=
  (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm).mpr le_rfl

lemma odd_part_is_odd' (m : ℕ) (hm : m ≠ 0) : 
    Odd (m / 2 ^ (m.factorization 2)) := by
  rw [Nat.odd_iff]
  by_contra h
  push_neg at h
  -- m / 2^a % 2 ≠ 1, so m / 2^a is even
  have h0 : (m / 2 ^ (m.factorization 2)) % 2 = 0 := by omega
  have h2dvd : 2 ∣ (m / 2 ^ (m.factorization 2)) := Nat.dvd_of_mod_eq_zero h0
  -- Then 2^{a+1} | m
  have h_pow_dvd : 2 ^ (m.factorization 2) * 2 ∣ m := by
    calc 2 ^ (m.factorization 2) * 2 
        = 2 ^ (m.factorization 2) * (m / 2 ^ (m.factorization 2) / (m / 2 ^ (m.factorization 2) / 2) * (m / 2 ^ (m.factorization 2) / 2)) := by sorry
      _ ∣ m := by sorry
  sorry
  
-- Actually let me try a cleaner approach
lemma odd_part_is_odd2 (m : ℕ) (hm : m ≠ 0) : 
    Odd (m / 2 ^ (m.factorization 2)) := by
  by_contra h
  rw [Nat.not_odd_iff_even] at h
  obtain ⟨c, hc⟩ := h
  -- m / 2^a = 2c, so m = 2^a * 2c = 2^{a+1} * c
  have hdvd := two_pow_factorization_dvd' m hm
  have h_eq : m = 2 ^ (m.factorization 2) * (2 * c) := by
    rw [← hc]; exact (Nat.mul_div_cancel' hdvd).symm
  have h_pow : 2 ^ (m.factorization 2 + 1) ∣ m := by
    rw [pow_succ, h_eq, mul_assoc]
    exact dvd_mul_right _ _
  exact Nat.pow_succ_factorization_not_dvd hm Nat.prime_two h_pow
    
EOF
lake env lean /tmp/test_odd_part.lean 2>&1 | head -10
```

```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_odd_part2.lean << 'EOF'
import Mathlib

lemma two_pow_factorization_dvd' (m : ℕ) (hm : m ≠ 0) : 2 ^ (m.factorization 2) ∣ m :=
  (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm).mpr le_rfl

lemma odd_part_is_odd' (m : ℕ) (hm : m ≠ 0) : 
    Odd (m / 2 ^ (m.factorization 2)) := by
  by_contra h
  rw [Nat.not_odd_iff_even] at h
  obtain ⟨c, hc⟩ := h
  -- hc : m / 2^a = c + c = 2*c
  have hdvd := two_pow_factorization_dvd' m hm
  have h_eq : m = 2 ^ (m.factorization 2) * (m / 2 ^ (m.factorization 2)) :=
    (Nat.mul_div_cancel' hdvd).symm
  have h_pow : 2 ^ (m.factorization 2 + 1) ∣ m := by
    rw [h_eq, hc, pow_succ]
    ring_nf
    exact dvd_mul_right _ _
  exact Nat.pow_succ_factorization_not_dvd hm Nat.prime_two h_pow

EOF
lake env lean /tmp/test_odd_part2.lean 2>&1 | head -10
```

```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_odd_part3.lean << 'EOF'
import Mathlib

lemma two_pow_factorization_dvd' (m : ℕ) (hm : m ≠ 0) : 2 ^ (m.factorization 2) ∣ m :=
  (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm).mpr le_rfl

lemma odd_part_is_odd' (m : ℕ) (hm : m ≠ 0) : 
    Odd (m / 2 ^ (m.factorization 2)) := by
  by_contra h
  rw [Nat.not_odd_iff_even] at h
  obtain ⟨c, hc⟩ := h
  have hdvd := two_pow_factorization_dvd' m hm
  have h_eq : m = 2 ^ (m.factorization 2) * (m / 2 ^ (m.factorization 2)) :=
    (Nat.mul_div_cancel' hdvd).symm
  have h_pow : 2 ^ (m.factorization 2 + 1) ∣ m := by
    rw [h_eq, hc, pow_succ (n := m.factorization 2)]
    calc (2 : ℕ) ^ m.factorization 2 * 2 ∣ 2 ^ m.factorization 2 * (c + c) := by
          apply Nat.mul_dvd_mul_left
          exact dvd_of_eq (by omega)
      _ = 2 ^ m.factorization 2 * (c + c) := rfl
  exact Nat.pow_succ_factorization_not_dvd hm Nat.prime_two h_pow
EOF
lake env lean /tmp/test_odd_part3.lean 2>&1 | head -10
```
The

> **Thinking:**
>  issue is that `h_pow` has the wrong goal since the rewrite changed the `m` too. Let me fix this by constructing the divisibility directly.


```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_odd_part4.lean << 'EOF'
import Mathlib

lemma two_pow_factorization_dvd' (m : ℕ) (hm : m ≠ 0) : 2 ^ (m.factorization 2) ∣ m :=
  (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm).mpr le_rfl

lemma odd_part_is_odd' (m : ℕ) (hm : m ≠ 0) : 
    Odd (m / 2 ^ (m.factorization 2)) := by
  by_contra h
  rw [Nat.not_odd_iff_even] at h
  obtain ⟨c, hc⟩ := h
  -- hc : m / 2^a = c + c = 2*c
  -- So 2 | (m / 2^a)
  have h2div : 2 ∣ (m / 2 ^ (m.factorization 2)) := ⟨c, by omega⟩
  -- So 2^{a+1} | m
  have h_pow : 2 ^ (m.factorization 2 + 1) ∣ m := by
    rw [pow_succ]
    exact Nat.mul_dvd_of_dvd_div (two_pow_factorization_dvd' m hm) h2div
  exact Nat.pow_succ_factorization_not_dvd hm Nat.prime_two h_pow
  
-- Hmm let me check if Nat.mul_dvd_of_dvd_div has the right type
#check @Nat.mul_dvd_of_dvd_div
-- (a b c : ℕ) (h₁ : a ∣ b) (h₂ : c ∣ b / a) : a * c ∣ b
-- Wait it's: a ∣ b → c ∣ b/a → a*c ∣ b
-- We have: 2^a ∣ m → 2 ∣ m/2^a → 2^a * 2 ∣ m
-- And 2^a * 2 = 2^{a+1} (with pow_succ)
-- So the types should match
EOF
lake env lean /tmp/test_odd_part4.lean 2>&1 | head -10
```


> **Thinking:**
> The issue is the argument order for `Nat.mul_dvd_of_dvd_div`. It takes `c ∣ b → a ∣ b / c → c * a ∣ b`. So I need:
> - `c = 2^a`, `b = m`, `a_arg = 2`
> - First arg: `2^a ∣ m` (which is `two_pow_factorization_dvd'`)  
> - Second arg: `2 ∣ m / 2^a` (which is `h2div`)
> - Conclusion: `2^a * 2 ∣ m`
> 
> 
> - Then I can simplify `2^a * 2` to `2^{a+1}` using `pow_succ`.


```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_odd_part5.lean << 'EOF'
import Mathlib

lemma two_pow_factorization_dvd' (m : ℕ) (hm : m ≠ 0) : 2 ^ (m.factorization 2) ∣ m :=
  (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm).mpr le_rfl

lemma odd_part_is_odd' (m : ℕ) (hm : m ≠ 0) : 
    Odd (m / 2 ^ (m.factorization 2)) := by
  by_contra h
  rw [Nat.not_odd_iff_even] at h
  obtain ⟨c, hc⟩ := h
  have h2div : 2 ∣ (m / 2 ^ (m.factorization 2)) := ⟨c, by omega⟩
  have h_mul : 2 ^ (m.factorization 2) * 2 ∣ m :=
    Nat.mul_dvd_of_dvd_div (two_pow_factorization_dvd' m hm) h2div
  have h_pow : 2 ^ (m.factorization 2 + 1) ∣ m := by
    rwa [pow_succ]
  exact Nat.pow_succ_factorization_not_dvd hm Nat.prime_two h_pow
EOF
lake env lean /tmp/test_odd_part5.lean 2>&1 | head -10
```
Now let me put it all together in the full test:
```bash
$ cd /home/jarred/code/erdos-410 && cat > /tmp/test_full_enters.lean << 'EOF'
import Mathlib

open ArithmeticFunction

-- Axiom stand-in for already-proven lemma
axiom sigma_iterate_ge_two_ax (n : ℕ) (hn : n ≥ 2) (k : ℕ) :
    (sigma 1)^[k] n ≥ 2

-- From codebase (proven)
lemma sigma_pow_two'_f (k : ℕ) : sigma 1 (2^k) = 2^(k+1) - 1 := by
  rw [sigma_apply_prime_pow Nat.prime_two]
  simp_rw [fun j => show 2^(j * 1) = 2^j from by ring_nf]
  have := Nat.geomSum_eq (by norm_num : (2 : ℕ) ≤ 2) (k + 1); simp at this; exact this

-- Helpers
lemma dvd_two_pow_sub_one_iff_f (q n : ℕ) :
    q ∣ 2^n - 1 ↔ (2 : ZMod q)^n = 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow n 2 (by omega))]
  simp [sub_eq_zero]

lemma q_dvd_sigma_two_pow_iff_f (q a : ℕ) :
    q ∣ sigma 1 (2 ^ a) ↔ orderOf (2 : ZMod q) ∣ (a + 1) := by
  rw [sigma_pow_two'_f, dvd_two_pow_sub_one_iff_f]
  exact orderOf_dvd_iff_pow_eq_one.symm

lemma orderOf_two_zmod_pos_f (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2) :
    orderOf (2 : ZMod q) ≥ 1 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have h2ne : (2 : ZMod q) ≠ 0 := by
    have : (2 : ZMod q) = ((2 : ℕ) : ZMod q) := by norm_cast
    rw [this, Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd; exact hodd (Nat.le_of_dvd (by omega) hdvd |>.antisymm hq.two_le)
  exact Nat.pos_of_ne_zero fun h0 =>
    (by have := hq.two_le; omega : q - 1 ≠ 0)
    (Nat.eq_zero_of_zero_dvd (h0 ▸ orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h2ne)))

lemma two_pow_factorization_dvd_f (m : ℕ) (hm : m ≠ 0) : 2 ^ (m.factorization 2) ∣ m :=
  (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm).mpr le_rfl

lemma odd_part_is_odd_f (m : ℕ) (hm : m ≠ 0) :
    Odd (m / 2 ^ (m.factorization 2)) := by
  by_contra h; rw [Nat.not_odd_iff_even] at h
  obtain ⟨c, hc⟩ := h
  exact Nat.pow_succ_factorization_not_dvd hm Nat.prime_two (by
    rw [pow_succ]; exact Nat.mul_dvd_of_dvd_div (two_pow_factorization_dvd_f m hm) ⟨c, by omega⟩)

lemma q_dvd_sigma_of_v2_dvd_f (q m : ℕ) (hm : m ≠ 0) 
    (hq : q ∣ sigma 1 (2 ^ (m.factorization 2))) :
    q ∣ sigma 1 m := by
  conv_rhs => rw [show m = 2 ^ (m.factorization 2) * (m / 2 ^ (m.factorization 2)) from
    (Nat.mul_div_cancel' (two_pow_factorization_dvd_f m hm)).symm]
  rw [isMultiplicative_sigma.map_mul_of_coprime
    (Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (odd_part_is_odd_f m hm)))]
  exact dvd_mul_of_dvd_left hq _

-- The key sorry
lemma v2_hits_residue_f (n : ℕ) (hn : n ≥ 2) (d : ℕ) (hd : d ≥ 1) :
    ∀ K, ∃ k ≥ K, d ∣ ((sigma 1)^[k] n).factorization 2 + 1 := by
  sorry

-- Main: prime enters infinitely often
lemma prime_enters_infinitely_f (q : ℕ) (hq : Nat.Prime q) (hodd : q ≠ 2)
    (n : ℕ) (hn : n ≥ 2) :
    ∀ K, ∃ k ≥ K, q ∣ (sigma 1)^[k] n := by
  intro K
  obtain ⟨k, hk_ge, hd_dvd⟩ := v2_hits_residue_f n hn
    (orderOf (2 : ZMod q)) (orderOf_two_zmod_pos_f q hq hodd) K
  have hne : (sigma 1)^[k] n ≠ 0 := by have := sigma_iterate_ge_two_ax n hn k; omega
  exact ⟨k + 1, by omega, by
    simp only [Function.iterate_succ', Function.comp_apply]
    exact q_dvd_sigma_of_v2_dvd_f q _ hne ((q_dvd_sigma_two_pow_iff_f q _).mpr hd_dvd)⟩
EOF
lake env lean /tmp/test_full_enters.lean 2>&1 | head -10
```
Everything compiles. Now let me integrate this into the main codebase:
```bash
$ cd /home/jarred/code/erdos-410 && tm update erdos410-zp6 --status "Integrating proven helper lemmas and reducing prime_enters_infinitely to v2_hits_residue"
```
Now let me update the main file with all the proven helper lemmas and the improved decomposition:
🛠️ **Executing tool: edit**

```bash
$ cd /home/jarred/code/erdos-410 && lake build 2>&1 | tail -15
```
Build succeeds with 3 sorrys (down from the original 1, but now much better structured). Let me verify:
```bash
$ cd /home/jarred/code/erdos-410 && grep -n "sorry" Erdos/Basic.lean
```

```bash
$ cd /home/jarred/code/erdos-410 && grep -B 3 "sorry" Erdos/Basic.lean
```
The 3 remaining sorrys are:

1. **`squarish_iterates_finite`** (line 793) — needs Zsygmondy's theorem (not in Mathlib)
2. **`v2_hits_residue`** (line 893) — needs Escape Lemma + Dirichlet arguments
3. **`prime_div_eventually_always`** (line 905) — persistence once entering

All other lemmas in the chain are fully proven:
- `prime_persistence` ✅ (from case split)
- `prime_persistence_two` ✅ (from `squarish_iterates_finite`)
- `prime_persistence_odd` ✅ (from `prime_enters_infinitely` + `prime_div_eventually_always`)
- `prime_enters_infinitely` ✅ (from `v2_hits_residue` + `q_dvd_sigma_two_pow_iff` + `q_dvd_sigma_of_v2_dvd`)
- Plus 10+ helper lemmas about ZMod order, odd parts, multiplicativity

Let me commit:
```bash
$ cd /home/jarred/code/erdos-410 && git add -A && git commit -m "Close prime_enters_infinitely; reduce to 3 atomic sorrys

Proven lemmas:
- two_ne_zero_zmod, orderOf_two_zmod_pos (Fermat's little theorem)
- dvd_two_pow_sub_one_iff (ZMod bridge)
- q_dvd_sigma_two_pow_iff (order characterization of q | σ(2^a))
- two_pow_factorization_dvd, odd_part_is_odd (2-adic decomposition)
- q_dvd_sigma_of_v2_dvd (multiplicativity + decomposition)
- prime_enters_infinitely (from v2_hits_residue + above)
- prime_persistence_odd (from prime_enters_infinitely + prime_div_eventually_always)

Remaining sorrys (3):
1. squarish_iterates_finite — needs Zsygmondy's theorem
2. v2_hits_residue — needs Escape Lemma + Dirichlet
3. prime_div_eventually_always — persistence argument"
```
