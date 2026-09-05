# Old Attempt Failures vs. the `v9.4` All-`n` Manuscript
**Date:** 2026-04-11  
**Purpose:** assess whether the failures, stalls, or overextensions in earlier LRC proof attempts are now explained by the more elegant all-`n` manuscript line culminating in `lrc_proof_v9_4.md`.

---

## Short answer

**Yes, mostly.**

The newer all-`n` manuscript explains a large fraction of the earlier failures by identifying the correct object more cleanly:

> LRC is a **coupled residue-coverage problem** in which support is rigid, non-unit support is subgroup-limited, and full coverage cannot be handed off indefinitely.

Most old attempts failed for one of three reasons:

1. they studied the **wrong level of description**,
2. they demanded a **stronger theorem than the classical LRC actually needs**, or
3. they had the **right intuition but the wrong local formalism**.

The `v9.4` manuscript does not make every earlier idea redundant. But it does explain, in a unified way, why many of those routes either stalled or overclaimed.

---

## The main retroactive explanation

The central `v9.4` claim is not “a thousand branch tricks happen to work.”

It is:

- runner coverage is **coupled, not freely assignable**,
- unit runners carry exclusive sole-cover responsibilities,
- non-unit runners live on rigid subgroup cosets,
- and floor-reset handoff is constrained by arithmetic coverage gates.

Once this is the lens, many old failures become intelligible:

- some routes were too continuous when the real object was discrete,
- some were too global when a local handoff obstruction was enough,
- and some were probing real structure but without the correct residue-ledger language.

---

## Route-by-route verdict

### 1. AP / extremal / complementary-pairs routes

**Verdict:** largely **explained and partially vindicated**.

The old AP-flavoured routes were not wrong to focus on rigid structure, but they often looked too special to generalise. The `v9.4` manuscript explains why they still mattered:

- AP-like structure was exposing **coupling rigidity**,
- complementary-pair phenomena were early local instances of non-free coverage assignment,
- but they were too tied to a particular extremal coordinate system to serve as the whole all-`n` proof.

So these routes did not fail because the structure was fake. They failed because they were **too specialised** to be the universal statement.

---

### 2. Missing-runner / clumping / pooled blocker routes

**Verdict:** **explained cleanly**.

These routes saw that many nominal blockers collapse into fewer effective blockers. The problem was that they did not yet have the right formal object.

`v9.4` explains them as early shadows of:

- coverage insufficiency,
- effective loss of independent support,
- and the impossibility of freely redistributing sole-cover obligations.

So the intuition was good. The old proofs failed because “clumping” and “empty slot” language was not yet precise enough to become a theorem.

---

### 3. Overlap-mass / `O_mass` / boundary-set global reduction routes

**Verdict:** **mostly explained as too strong / too high-level**.

These routes were trying to control a very global obstruction functional. That was a legitimate mathematical object, but it asked for more than the classical all-`n` existence claim needs.

The new manuscript wins at a lower and cleaner resolution:

- static sole-cover exposure,
- dynamic floor-reset handoff failure,
- subgroup rigidity for non-units.

So the old overlap-mass attempts were often trying to prove a global saturation theorem when the actual theorem only needed a **single unavoidable exposed residue or safe event**.

In other words:

> they were often aiming at a stronger shadow of the truth than was necessary.

---

### 4. Outside-band safe-mass / period-summed positivity routes

**Verdict:** **partly explained**.

These routes correctly sensed that safe mass can live outside the most obvious local band. That insight remains valuable.

What `v9.4` explains is why these routes were hard to close:

- they were working at a period/global-resolution object,
- while the newer proof often closes branches already at the static or local-reset level.

So these attempts were not barking up the wrong tree; they were just trying to close the problem at a **higher resolution than needed**.

---

### 5. Non-unit `z=0`, NZ0, coset-essentiality, subgroup-opacity routes

**Verdict:** **strongly vindicated and explained**.

This is one of the clearest cases where the new manuscript explains the old frontier.

Those notes were close to the real local obstruction, but they lacked one or more of:

- the correct orientation (`Leave_e`, not `Enter_e`),
- the right branch integration,
- or the exact way unit and non-unit behavior interact.

`v9.4` explains why these routes felt fundamental:

- they were studying the real local event where support can fail,
- and the new proof’s dynamic half is exactly a handoff-failure story.

So these did not fail because the phenomenon was marginal; they failed because the final global language had not yet crystallised.

---

### 6. 2025 ergodic / Brascamp-Lieb / Fubini-transversality routes

**Verdict:** **explained, but more as “wrong resolution” than “wrong instinct.”**

These older routes looked at generic/resonant geometry, positive measure, and torus intersection. That was useful architecture, but too coarse to be the final all-`n` proof engine.

The new manuscript explains the limitation:

- the real hard core is arithmetic residue coverage during the active interval,
- not just large-scale positive measure on a torus.

So those routes were not useless; they captured:

- why structure class matters,
- why the problem has geometric stratification,
- and why generic vs resonant behavior feels different.

But they did not isolate the discrete support obligations sharply enough.

---

### 7. Transport / CRT / discrete torus / coverage-capacity routes

**Verdict:** **vindicated most strongly**.

These are the old attempts most clearly explained by the new manuscript, because they were already closest to the final object.

The newer all-`n` manuscript effectively says:

- yes, the problem is about transport of support,
- yes, the residue system is the right arena,
- yes, non-unit support is rigid and sparse,
- and yes, persistent full obstruction fails because handoff is arithmetically constrained.

So this family did not really “fail” mathematically. It was the **proto-final language** that eventually got simplified and stabilised.

---

### 8. Finite-window certifications and empirical packs

**Verdict:** **explained as evidence of the right mechanism, but not proof.**

The new manuscript clarifies why these could never serve as theorem authority on their own:

- they were exact evidence packs,
- not analytic closure,
- and they became misleading only when promoted beyond their scope.

Still, many of them were useful because they were sampling the correct objects:

- chamber persistence,
- period-safe mass,
- non-unit exit anatomy,
- and relay/handoff events.

So their “failure” was mostly one of **status inflation**, not uselessness.

---

## What kinds of old failure are now explained?

### A. Wrong level of description

Common old pattern:
- continuous geometry,
- broad measure claims,
- or whole-period positivity,

when the real proof only needed:
- one exposed residue,
- one failed handoff,
- or one safe fibre.

`v9.4` explains these failures by moving to the residue-coverage level.

---

### B. Stronger-than-necessary theorem targets

Common old pattern:
- trying to prove full occupancy positivity,
- global overlap inequalities,
- or broad safe-mass theorems,

when classical LRC only needs:
- `x_0 >= 1`.

`v9.4` wins partly because it is more modest in what it asks the machinery to prove.

---

### C. Right phenomenon, wrong formalism

Common old pattern:
- good local intuition,
- but wrong local event criterion,
- wrong scope of a lemma,
- or unjustified independence step.

`Enter_e` versus `Leave_e` is the cleanest example of this.

The new manuscript explains these as local formal mistakes around a basically real phenomenon.

---

### D. Status / packaging failures rather than mathematical failures

Common old pattern:
- exact certifications presented as if they were theorem closure,
- route memos presented as if they were canonical,
- stale ledgers overriding newer manuscript lines.

The newer manuscript does not just solve math; it also shows that many old “failures” were really failures of **presentation, scope control, or packaging discipline**.

---

## What is *not* fully explained?

Not every old route is now fully subsumed.

Two caveats remain:

1. Some older global objects still contain mathematical insight not yet fully compressed into the final manuscript language, especially:
   - period-summed safe mass,
   - outside-band structure,
   - and some occupancy-deficit / master-theorem perspectives.

2. Some older AP or chamber-based routes may still contain sharper quantitative information than the streamlined existence proof needs.

So the new manuscript explains most old failures, but it does **not** mean all older ideas have become obsolete.

---

## Final verdict

The cleanest overall answer is:

> **Yes. The newer all-`n` solution explains most of the old failures by revealing that the real object is coupled residue coverage with rigid support obligations and arithmetically constrained handoff.**

More specifically:

- old routes built around rigidity, transport, cosets, or handoff were mostly **on the right track**;
- old routes built around very broad geometric or global positivity claims were often **too coarse or too ambitious**;
- and many empirical/certification routes failed only because they were **evidence, not theorem statements**.

So the elegant `v9.4` line is not just a new proof. It is also a **retroactive explanation** of why the earlier search behaved the way it did.
