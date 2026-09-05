# LRC Master Theorem Synthesis v1

## Purpose

This note switches from branch-audit mode to synthesis mode.

The working thesis is that the remaining `n=all` program is not blocked by a dozen unrelated local lemmas. It is blocked by one missing structural theorem about **persistent full obstruction on the residue circle**.

The point of this note is to state that candidate theorem cleanly, show how the already-built machinery fits into it, and separate:

- what is already theorem-grade,
- what is strong structural evidence,
- and what the one genuine remaining closure problem appears to be.

The goal is not to claim closure. The goal is to identify the right object.

---

## Executive Thesis

The global mechanism suggested by the current proof program is:

> **Persistent full support is impossible because residue coverage has finite transport capacity under the jump schedule.**

Everything already built points to this.

- **Sole Cover** identifies residues with unique support at the floor-0 extreme.
- **Cond1/Cond2** gives the exact local handoff rule at unit `z=0` events.
- **O1 deficit transport** gives the exact conservation law for how multiplicity moves across cells.
- **Composite transparency / opacity** shows non-unit runners cannot maintain uniform support all the time; they are structurally intermittent.

These do not look like four different proofs. They look like four coordinate charts on one system:

> a discrete dynamical system of residue multiplicities over the cell partition of the divisible band.

---

## The Shared Object

Fix a Case-2 tuple `E`, let

`L = lcm(E)`,

and partition the divisible band by the jump set into half-open cells

`C_i = [J_i, J_{i+1})`.

On each cell:

- the floor vector `tau_i = (floor(e alpha))_{e in E}` is constant;
- each runner has an exact congruence bad set `bad_e(tau_i)`;
- the total obstruction set is
  `U_i = union_{e in E} bad_e(tau_i)`;
- the residue multiplicity is
  `m_i(r) = #{e in E : r in bad_e(tau_i)}`.

Then:

- `C_i` is **blocked** iff `U_i = Z_n`;
- `C_i` is **safe** iff `U_i != Z_n`.

At each boundary `beta`, only the jumping runners change coverage. So full obstruction is not a static covering question. It is a **transport question**: can the system keep `m_i(r) >= 1` for every residue while coverage is continually handed off?

That is the common language of all remaining branches.

---

## Candidate Master Theorem

### Master Theorem MT (Persistent Full Obstruction Is Impossible)

Let `E` be a normalized gcd-1 tuple and consider the exact cell decomposition of the divisible band.

Assume every coordinate projection that matters is active, so each boundary event is governed by the exact congruence bad-set dynamics. Then there exists no blocked chain whose length exceeds the intrinsic transport threshold of the family.

Equivalently:

> there must exist a cell `C_i` with `U_i != Z_n`.

In residue language:

> some residue must eventually become under-supported because the jump schedule cannot indefinitely realize a complete handoff at every boundary.

This theorem is still conjectural in full generality. But it is the natural master statement sitting behind the current program.

---

## Why This Is the Right Unifier

### 1. Sole Cover is the static extreme of the same theorem

At the floor-0 interval, certain residues are uniquely supported by specific unit runners.

Dropping one of those runners exposes a residue immediately. This is not a different mechanism from O1. It is the zero-transport limit:

- initial multiplicity is already `1`,
- the support defect is present without any boundary evolution.

So Sole Cover is the simplest manifestation of transport failure.

### 2. Cond1/Cond2 is the exact local transition law

The corrected unit coverage criterion says that at a unit `z=0` event, another unit runner covers the departing residue if and only if one of two arithmetic handoff conditions fires:

- `Cond1`: exact lower-side synchronization,
- `Cond2`: wrap-around upper-side synchronization.

This is not just a repair to one proof. It is the exact residue-handoff rule.

So `Cond1/Cond2` supplies the local dynamics needed for any master theorem about persistent full obstruction.

### 3. O1 deficits are the conservation law

The prefix deficit identity

`m_k(r) - 1 = b_start(r) + Adds_r(k) - Drops_r(k)`

is the exact bookkeeping relation for residue support.

This is the cleanest statement currently available in the whole program. It says:

- blocked continuation is equivalent to non-overdraft at every residue,
- break occurs exactly when some residue overdrafts its initial redundancy.

So O1 is not a separate side-project. It is the dynamical core of the master theorem.

### 4. Composite transparency is the non-unit sparsity law

For non-units with `g = gcd(e,n) > 1`, coverage is not uniform:

- support lives on cosets,
- transparent states exist when `g >= 3`,
- `g = 2` runners are never transparent but still only move within rigid coset geometry.

This means non-unit runners cannot behave like a uniformly available repair network. Their support is arithmetically sparse and temporally intermittent.

So composite-specific behavior is not alien to the unit transport picture. It is the non-unit half of the same finite-capacity phenomenon.

---

## The Master Problem in One Sentence

The remaining problem is to prove that:

> the residue-transport system cannot realize a perfect handoff forever.

That is all.

The branch explosion only appears because this statement manifests differently in different regimes:

- dropped-unit regime: immediate exposed residue,
- prime counting regime: period-miss surplus,
- one-divisible composite regime: thin residues and failed handoffs,
- multi-divisible regime: the same transport problem with more non-unit structure.

But the geometry underneath is one geometry.

---

## Branch Dictionary

This is the branch-to-master-theorem translation map.

### Dropped unit / floor-0 branches

Master-theorem reading:

- there exists a residue with initial multiplicity `0` or `1`,
- no transport is needed to produce a miss.

### Prime `n`, period-counting branches

Master-theorem reading:

- the obstruction system fails on enough periods that the safe count is positive;
- in other words, persistent full support already fails at the period level.

### O1 blocked-chain program

Master-theorem reading:

- full support can persist only if every residue handoff is solvent;
- the conjectural part is that bounded-time solvent transport is impossible.

### Composite `p^k`, B3-type branches

Master-theorem reading:

- unit runners alone leave arithmetic residue classes thin;
- non-unit runners have intermittent or coset-restricted support;
- together they should be unable to maintain full support throughout the band.

### Multi-divisible composite branches

Master-theorem reading:

- same transport problem,
- but with several non-unit channels active simultaneously.

This is not a different problem. It is the same theorem with a larger non-unit transport subgraph.

---

## The Most Credible Master-Theorem Route

At the current state of the program, the most credible path is:

### MT.1 Residue-Local Ledger

Already proved in O1 form:

- multiplicity update identity,
- prefix deficit identity,
- residue-level break criterion.

This should be treated as the permanent bookkeeping layer.

### MT.2 Thin-Residue Existence

Need a theorem identifying at least one residue or small residue family with genuinely limited repair capacity.

The correct object is probably not a specific residue label like `2`, but one of:

- low-capacity residue classes,
- low-multiplicity residues at chain start,
- arithmetic residue families poorly served by non-unit cosets.

### MT.3 Forced Handoff Failure

Need a theorem that the exact jump schedule cannot keep the thin residue(s) solvent forever.

This is the current missing step in O1 language.

### MT.4 Safe-Cell Consequence

Once solvent transport fails, some residue becomes uncovered, so a safe cell appears.

Then:

- for existence, `x_0 > 0` follows immediately;
- for stronger bounds, counting or measure arguments can be layered on top.

---

## What Is Already Strong Enough To Reuse

The following components already look master-theorem-grade:

- exact congruence bad-set formalism,
- floor-state cell decomposition,
- boundary transport counts,
- prefix deficit identity,
- singleton break certificate,
- corrected unit coverage rule `Cond1/Cond2`,
- non-unit transparency / coset structure,
- exact bridge between safe cells and safe-fibre count when using the full tuple lattice.

These should not be treated as isolated branch artifacts anymore. They are the current axioms of the master system.

---

## What Is Still Missing

The following are still not closed:

- a theorem forcing deficit overflow in bounded time;
- an exact thin-residue theorem that works uniformly across the composite regimes;
- a unified argument covering both one-divisible B3-type and multi-divisible composite obstruction.

So the synthesis conclusion is not “the proof is done.”

It is:

> the project now appears to have one remaining structural theorem, not many unrelated local gaps.

---

## Honest Status

### Proved structural layer

- cell dynamics,
- residue multiplicity bookkeeping,
- local break certificates,
- corrected unit handoff rule,
- several special branches and floor-0 regimes.

### Conjectural master layer

- persistent full-support impossibility in bounded time,
- equivalently, universal forced handoff failure.

### Strategic conclusion

The right next phase is not more branch-auditing.

It is to formulate and attack the master theorem:

> **No family in the remaining Case-2 regimes can sustain full residue support throughout the divisible band, because residue coverage transport has finite arithmetic capacity under the boundary schedule.**

---

## Recommended Next Work

1. Rewrite the remaining open branches in this residue-transport language.
2. Treat O1.D1 / O1.D2 as master-system lemmas, not as branch-local curiosities.
3. Search for a thin-residue theorem that simultaneously explains:
   - dropped-unit exposure,
   - composite transparency failure,
   - and bounded-time transport insolvency.
4. Demote branch-specific heuristics that are really shadows of the same transport statement.
5. Use empirical scans only to guess the right thin-residue object, not to certify closure.

---

## Closing View

The project does not currently look like it needs ten more unrelated lemmas.

It looks like it needs one theorem stating that **coverage can move, but not indefinitely self-heal**.

That is the most credible candidate for the missing `n=all` mechanism.
