# Overseer Notes — Erdős #410 Proof Project

## Session 1 — 2026-02-07

### Project Setup (14:34 UTC)
- **Goal**: Prove Erdős Problem #410 in Lean 4 / Mathlib — iterated σ grows super-exponentially
- **Workflow**: Math workflow (advisor / execute / verify agents)
- **Initial State**: Empty backlog, single `Erdos/Basic.lean` with `sorry`

### DAG Bootstrap (14:34 UTC)
- Created root advisor task. Advisor built a 14-task DAG before crashing and wiping the backlog.
- Manually recreated 15-task DAG based on observed plan.

### Risk Assessment
- **HIGH RISK**: This is an *open conjecture* in number theory. No known proof exists.
- Elementary bounds (σ(n) ≥ n+1) only give exponential growth, not super-exponential.
- Formalizing deep number theory in Lean is its own challenge.

### Check-in 1 — 14:55 UTC

**Status**: 2 of 15 tasks closed (L1.1, L1.2). Worker now on L3.1.

**First worker run (advisor task)**: Crashed and wiped the backlog. The advisor built a good DAG but something caused the backlog to be emptied. Had to manually recreate. **Lesson**: Worker process is fragile; should investigate root cause.

**Intervention**: Ran `lake exe cache get` to download 7869 pre-built Mathlib oleans. This was the single biggest unblock — worker was building Mathlib from source which would have taken hours.

**L1.1 completed** (~20 min): Proved `sigma_one_ge` using `sigma_one_apply`, `Finset.single_le_sum`, `Nat.mem_divisors_self`. Also fixed `@[reducible]` attribute bug.

**L1.2 completed** (~8 min): Proved `sigma_one_ge_succ` using `Finset.sum_pair` and `Finset.sum_le_sum_of_subset`. Clean, readable proof.

**Workflow quality observations**:
- ✅ Worker correctly searches Mathlib API with grep before writing proofs
- ✅ Writes test files to validate before committing
- ✅ Clean proof style with doc comments
- ✅ Priority scheduling working — jumps to higher-priority tasks
- ⚠️ Sequential execution — no parallelism
- ⚠️ Skipped verification tasks to prioritize execution (correct by priority rules)

### Check-in 2 — 15:39 UTC

**Course correction**: The agents gave up on L3.2 by declaring it an "open conjecture" and closing everything as blocked. The advisor wrote a STATUS.md documenting surrender. User rightfully pushed back — being open is the whole point.

**Action taken**: 
- Reopened L3.2, L4, V4
- Created three concrete attack tasks:
  - **A1** (erdos410-ayc): Prove σₖ(n) is eventually always even (σ odd ⟺ n is square or 2×square)
  - **A2** (erdos410-9x2): If eventually even, prove compounding growth → super-exponential (needs abundancy from accumulating prime factors, not just fixed 3/2 base)
  - **A3** (erdos410-k7y): Prove ω(σₖ(n)) → ∞ via multiplicativity of σ introducing new prime factors

**Key mathematical insight in task descriptions**: Even just showing "eventually always even" only gives exponential base 3/2. For *super*-exponential, we need the multiplicative ratio σ(m)/m to grow, which requires showing prime factors accumulate. The multiplicativity σ(2m) = 3σ(m) for odd m is a crucial building block.

**Lesson for the agentic workflow**: The "escalate as open" behavior is a failure mode. Need to bias agents toward attempting proofs rather than researching why they can't. Writing STATUS.md about why you can't do something is not progress.

---
