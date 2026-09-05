# Dropped-Unit Overarching Structure Strategy

Date: 2026-04-12
Status: strategy note

## 1. Guardrail

The current danger is clear:

> do not turn the repair into an exception catalogue.

The `n=8` outlier was useful because it exposed a mechanism, not because it created a new special branch to manage forever.

So the right strategic rule is:

> every local exception we keep must be retained only as evidence for a broader invariant.

If a statement does not point toward an invariant shared by the whole dropped-unit branch, it is not the next theorem target.

## 2. What the outlier actually taught us

The `n=8` prototype contributed three genuinely structural lessons.

### 2.1 The right local object is a patching runner

At the base fibre `b_0=L/n`, a missing unit target `r_d=-d^{-1}` is not controlled by residue support alone.
It is controlled by actual retained speeds `e=nq+\rho` satisfying

- `rho ≡ qd (mod n)`, or
- `rho ≡ (q+1)d (mod n)`.

This is not an exception-specific fact. It is the exact local geometry of the whole problem.

### 2.2 The right dynamic object is burden migration

The first safe fibre need not occur:

- at the canonical target `r_d`,
- at the original patcher,
- or at that patcher’s next reset.

So the repair theorem must track **migration of a thin burden**, not a fixed residue or a fixed runner.

### 2.3 The right obstruction is finite transport capacity

The March archive already isolated the single-runner part:

- a unit runner can carry a fixed residue only across one two-state block,
- a non-unit runner can carry a fixed residue or fixed coset only across one two-state block,
- `g=2` non-units have no transparency gap, but still only change effectively every second event.

So the real open theorem is not local support algebra. It is the chain-level claim that these bounded episodes cannot be strung together forever while maintaining full coverage.

## 3. The invariant we should now target

The best candidate overarching invariant is:

> **thin burden at the base fibre plus bounded transfer capacity along the event path.**

This has two parts.

### Part A. Thin base-fibre object

We need a theorem that the fully covered base fibre in the dropped-unit branch is still thin in some uniform sense.

The cleanest candidate is:

> there exists a residue of multiplicity `1` at `b_0`.

This is attractive because it is:

- branch-wide,
- residue-transport native,
- and exactly the kind of object the March transport notes already wanted.

### Part B. Transfer cannot remain solvent forever

Once a multiplicity-`1` residue exists, later events can do only three things:

1. expose it immediately;
2. keep it alive by the same runner for one bounded episode;
3. transfer the burden to another runner or another residue.

The local episode lengths are already controlled. So the missing theorem is:

> the burden-transfer chain cannot persist through all of `B_div`.

That is the real transport-instability theorem.

## 4. Why the multiplicity-1 target is promising

Bounded scans currently show two striking facts.

### 4.1 Empirical fact

In all scanned dropped-unit tuples with full coverage at `b_0`,

- `n=5` with speeds `<=3n`,
- `n=6` with speeds `<=3n`,
- `n=7` with speeds `<=2n`,
- `n=8` with speeds `<=2n`,

the minimum base-fibre multiplicity is always exactly `1`.

### 4.2 Stronger empirical pattern

In those same scans, the total incidence count

`I_0 := sum_r m_0(r)`

always satisfies

`I_0 < 2n`.

Hence a full-cover base fibre cannot have all multiplicities at least `2`.

This strongly suggests that a multiplicity-`1` lemma may be a consequence of a more basic incidence inequality, not just a direct combinatorial accident.

That is exactly the kind of theorem we want:

- it is not an exception theorem,
- it is a general structural inequality.

## 5. The right proof posture

We should therefore avoid the following trap:

> “prove a separate repair lemma for each exceptional mechanism.”

Instead the proof programme should be:

1. prove a **base-fibre thinness lemma**;
2. prove a **bounded transfer lemma**;
3. combine them into dropped-unit transport instability.

The `n=8` outlier is then a prototype witness for step 2, not a permanent sub-branch.

## 6. Best immediate theorem target

The most structural next target is:

### Target BF.1 (base-fibre thinness)

In the dropped-unit branch, if the base fibre `b_0=L/n` is fully covered by the retained non-divisible runners, then some residue has multiplicity `1` at `b_0`.

The best way to prove this is likely not by residue-by-residue casework, but by an incidence bound of the form

`I_0 < 2n`.

That would automatically imply the existence of a multiplicity-`1` residue under full coverage.

## 7. Why this respects the overarching structure

This strategy is faithful to the larger all-`n` narrative:

- not “the exception has its own custom fix,”
- but “the exception revealed the correct invariant.”

So the hierarchy is:

- local formulas identify patchers,
- thinness identifies where the burden lives,
- transport instability explains why full obstruction cannot persist.

That is the overarching structure that explains all branches, including the exceptions.
