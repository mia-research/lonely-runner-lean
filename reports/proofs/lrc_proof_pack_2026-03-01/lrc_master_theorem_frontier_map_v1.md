# LRC Master Theorem Frontier Map v1

## Purpose

This note rewrites the current frontier in the language of the candidate master theorem from
[lrc_master_theorem_synthesis_v1.md](/Users/trentpalelei/Documents/Claude%20Library/lrc_master_theorem_synthesis_v1.md).

The goal is to stop treating the open branches as disconnected local defects. Instead, each branch is mapped to the same structural question:

> can the obstruction system maintain full residue support throughout the relevant domain, or must some miss cell / safe time appear?

This note is a translation layer, not a new proof.

---

## The Master-Theorem Lens

The synthesis thesis is:

> **Persistent full obstruction is impossible because residue coverage has finite transport capacity under the jump schedule.**

This can appear in four different forms:

1. **Static exposure**
   A miss exists immediately at a special floor state such as floor 0.

2. **Period-level failure**
   A whole period or period class fails to maintain full support often enough to force a safe count.

3. **Dynamic transport failure**
   Full support can persist only if every residue handoff remains solvent; eventually some residue must overdraft.

4. **Ambient torus intersection**
   In the irrational branch, the same “safe region is nonempty” problem appears as intersection of a subtorus with the safe box.

Every current branch can be placed in one of these four forms.

---

## Master Problem Compression

The current frontier compresses to four master problems.

### MP-I: Static Exposure

Question:

> Is there an explicit floor state or band where some residue is visibly unsupported?

This is the Sole Cover / floor-0 style mechanism.

### MP-II: Period-Level Failure

Question:

> Can full support fail often enough across periods or period classes to force a positive safe count?

This is the prime counting-bridge mechanism and its relatives.

### MP-III: Dynamic Transport Failure

Question:

> If full support holds on a blocked chain, can the residue ledger stay solvent forever under the exact boundary schedule?

This is the O1 / O2 / composite-no-dropped-unit mechanism.

### MP-IV: Torus-Box Intersection

Question:

> Does the closure subtorus of the irrational orbit intersect the open safe box?

This is the intermediate-rank irrational problem.

---

## Branch Clusters

The entire program now looks like three closed clusters and one open synthesis cluster.

### Cluster A: Already Closed by Static Exposure

- prime and composite dropped-unit floor-0 branches,
- Sole Cover branches,
- near-complete floor-0 miss cases,
- B3a at `n=9`.

These all solve the master theorem immediately at a distinguished initial state.

### Cluster B: Already Closed by Period-Level Failure

- prime one-divisible counting-bridge branches,
- prime multi-divisible regular/bad-period branches,
- prime period-zero miss machinery.

These do not need residue-transport forcing; the support defect is already visible at the period level.

### Cluster C: Open Dynamic Transport Cluster

- composite one-divisible no-dropped-unit branches,
- B2 achievability-style branches,
- B3b (`n = p^k`, `p >= 5`),
- multi-divisible composite branches,
- O1 run-cap forcing,
- O2 safe-count forcing.

This is the main remaining structural cluster.

### Cluster D: Open Torus Intersection Cluster

- irrational intermediate-rank branch `2 <= r <= n-2`.

This is conceptually parallel to the master theorem, but lives in the ambient torus setting rather than the rational cell-dynamics setting.

---

## Branch-by-Branch Translation

### 1. Irrational Rank-1 Branch

Current reading:

- all speeds are rational multiples of one irrational;
- reduces to the rational branch after clearing denominators.

Master-theorem reading:

- not a new mechanism;
- simply a reduction into the rational obstruction system.

Status:

- closed modulo the rational branch it reduces to.

### 2. Irrational Full-Rank Branch

Current reading:

- full Kronecker density gives visits to every open subset of the ambient torus.

Master-theorem reading:

- the safe box is nonempty and the whole torus is available;
- no fine obstruction analysis is needed.

Status:

- closed.

### 3. Irrational Intermediate-Rank Branch

Current reading:

- subtorus `T` has full coordinate projections but is not the whole torus;
- need `T ∩ B != empty`.

Master-theorem reading:

- ambient torus analogue of “some safe state must exist”;
- this is the geometric version of the transport impossibility problem.

Status:

- open.

Remaining subproblem:

- prove a torus-intersection theorem or an equivalent Fourier/subtorus lemma.

### 4. Rational Case 1 (`n` divides no speed)

Current reading:

- explicit arithmetic witness gives safe times directly.

Master-theorem reading:

- persistent obstruction fails immediately by explicit construction.

Status:

- closed.

### 5. Prime `n`, One-Divisible, Dropped Unit

Current reading:

- Sole Cover at floor 0 exposes a unique residue on the floor-0 band.

Master-theorem reading:

- static exposure with no transport needed.

Status:

- closed.

### 6. Prime `n`, One-Divisible, No Dropped Unit

Current reading:

- period-zero miss and counting bridge force positive safe count.

Master-theorem reading:

- period-level failure of persistent full support.

Status:

- closed in the prime track.

### 7. Prime `n`, Multi-Divisible

Current reading:

- regular/bad period split closes via period-level analysis.

Master-theorem reading:

- same as above: persistent full support already fails at the period layer.

Status:

- closed in the prime track.

### 8. Composite `n`, One-Divisible, Dropped Unit

Current reading:

- Sole Cover gives `x_0 >= 1`;
- stronger `x_0 >= phi(n)` still needs the composite counting bridge.

Master-theorem reading:

- LRC existence is already closed by static exposure;
- only a strengthening statement remains.

Status:

- LRC existence closed,
- strengthening still open.

### 9. Composite `n`, One-Divisible, B1 (Even / floor-0 accessible branches)

Current reading:

- handled by explicit floor-state geometry.

Master-theorem reading:

- static exposure.

Status:

- closed, assuming the current branch classification remains correct.

### 10. Composite `n`, One-Divisible, B2 (Odd with at least two prime factors)

Current reading:

- mod-`q` obstruction route seems correct but still needs achievability of the target floor configuration.

Master-theorem reading:

- thin residue / arithmetic-class exposure should exist;
- current gap is not the transport law itself, but reaching the right state where the exposure is visible.

Status:

- nearly closed but still open analytically.

Remaining subproblem:

- achievability / realization of the needed floor state.

### 11. Composite `n`, One-Divisible, B3a (`n = 9`)

Current reading:

- both non-units are dropped;
- floor-0 leaves only units in the fixed set, so non-unit residues miss immediately.

Master-theorem reading:

- static exposure in a special prime-power edge case.

Status:

- closed.

### 12. Composite `n`, One-Divisible, B3b (`n = p^k`, `p >= 5`)

Current reading:

- floor-0 closes nothing,
- simultaneous transparency route fails,
- corrected `Cond1/Cond2` shows the local handoff law,
- `m=1` no longer supports the old Z0S count.

Master-theorem reading:

- the branch is an unresolved dynamic transport problem with non-unit sparsity.

This is the purest current instance of the master theorem:

- units provide part of the repair network,
- non-units are intermittent and coset-restricted,
- the question is whether full support can persist through the whole band.

Status:

- open.

Remaining subproblem:

- prove forced transport failure or positive average miss in this prime-power composite regime.

### 13. Composite `n`, Multi-Divisible

Current reading:

- still depends on the same unresolved Gap-A style mechanism.

Master-theorem reading:

- same transport problem as B3b, but with more non-unit channels.

Status:

- open.

Remaining subproblem:

- identify the thin-residue / low-capacity object that survives the presence of multiple non-unit channels.

### 14. O1 Run-Cap Program

Current reading:

- exact prefix deficit identity and break criterion are proved;
- forcing bounded-time deficit overflow is open.

Master-theorem reading:

- this is the core dynamic form of the master theorem.

Status:

- local mechanics closed,
- forcing open.

### 15. O2 Safe-Count Program

Current reading:

- safe-mass and exact cell-count identities are promising,
- but full closure still needs a theorem forcing enough safe mass.

Master-theorem reading:

- quantitative version of the same transport failure:
  not just “some miss exists,” but “enough miss exists.”

Status:

- open.

---

## What Is Truly Shared Across the Open Cluster

The open rational branches all appear to need the same three ingredients.

### Shared Ingredient 1: A Thin Residue Object

Need one residue or small residue family with limited repair capacity.

Possible forms:

- low initial multiplicity,
- low chain-local coverer capacity,
- poor access to non-unit cosets,
- arithmetic class starved by the jump schedule.

### Shared Ingredient 2: Exact Transport Bookkeeping

Already available:

- exact bad-set dynamics,
- boundary handoff counts,
- prefix deficit identity,
- singleton break certificate.

### Shared Ingredient 3: A Forcing Theorem

Still missing:

> the jump schedule cannot keep the thin residue object solvent forever.

This is the shared missing theorem behind O1, O2, B3b, and multi-divisible composite branches.

---

## The Frontier After Translation

After translation into master-theorem language, the frontier is much smaller.

### Closed or mostly closed

- static exposure cluster,
- prime counting cluster,
- rank-1 reduction,
- full-rank irrational branch,
- composite dropped-unit existence.

### Still genuinely open

1. **Intermediate-rank irrational torus intersection**
2. **Dynamic transport failure in the composite no-dropped-unit cluster**
3. **Composite strengthening statements (`x_0 >= phi(n)` rather than just existence)**

That is a far cleaner picture than the raw branch list.

---

## Practical Consequence

The proof program should stop speaking as if B3b, multi-divisible composite, O1, and O2 are separate species.

They are one species:

> **can a sparse repair network on residues keep full support alive under asynchronous boundary transport?**

That is the open question.

---

## Recommended Next Synthesis Tasks

1. Promote the language of residue multiplicity, handoff, and deficit into the main proof draft.
2. Rewrite B3b and multi-divisible composite notes in the same transport language as O1.
3. Stop proposing branch-specific rescue lemmas unless they clearly instantiate one of:
   - thin-residue existence,
   - exact transport bookkeeping,
   - forced handoff failure.
4. Keep the irrational intermediate-rank problem separate but conceptually parallel: it is the torus version of “safe region must be hit.”

---

## Bottom Line

The current proof pack no longer looks like it is missing many local facts.

It looks like it is missing:

- one geometric theorem in the irrational intermediate-rank setting, and
- one transport theorem in the composite rational setting.

Everything else is increasingly just notation, bookkeeping, or branch-specific shadow of those two problems.
