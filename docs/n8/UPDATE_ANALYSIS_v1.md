# Update analysis: the five hubs and the five open items

2026-09-17. Input to the update discussion. **Not a plan.** For each hub and each open item: what it
currently says, what today's work bears on it, what it touches, and where the risk of dropping or
importing sits. Questions for the author are marked **Q**.

Baseline: `experiments/n8/manuscript_map_v9_1.json`.

---

## The five hubs

### §6.7 Existence — cited by 7 (§4.5, §6A, §8.2, §9, §10, App A, App C)

**Highest-ripple section in the document, and where today's work lands.** Currently: the statement
`[OPEN; not stated in either artefact]`, "what is proved of it", "what failure would require", the
per-runner obligation, and the computations.

Bearing on it from today: the `U`/`K` calculus (8 new `Flanks` declarations); 4,475 census family
theorems; and `CascadeCapped ↔ ExistenceAt8`, which says the whole obligation is a uniform cap on the
cascade's instants.

**Risk — importing.** `U_e`, `K_e`, "killer lattice", "uncovered residues" are the parallel machine's
vocabulary, not §0's. The objects underneath are native (openings, residues, the clearing test), but the
names are not. **Q: do these enter the manuscript under these names, under framework names, or not at
all?**

**Risk — dropping.** This section carries one of the five open items (line 492). Whatever happens to it,
the `[OPEN]` must survive and the gate's check [4] must keep matching.

### §6.9 Flanks — cited by 7 (§1.1, §4.5, §6.7, §8.2, §9, §10, Abstract)

Currently: the mirror of Theorem 4.8 `[DERIVED]`, the flank computations `[VERIFIED]`, and **two named
open items** — flanks with four or more non-integer ratios, and "not every flank of a runner can be
shadowed at once, which is Existence read at flanks".

Bearing on it: `lonely_iff_exists_flank` is the equivalence this section rests on and is already cited.
The census families are flank results — each is "this arrangement is lonely at this flank's opening".

**Q: does the census belong here or in §4.5?** It is family material, and §4.5 is "Families in which
Existence holds at once"; but §6.9 is where flanks live. The map says both are hubs, so the choice
ripples either way.

### §5 No external dependency — cited by 7

**The nativeness anchor.** It claims: one v7 citation, now derived in Lean at general `n`; "Nothing else
is cited: no equidistribution, no result at another order, no proof sketch."

**Risk — this is the section an import would falsify.** Anything added elsewhere that quietly depends on
outside work makes §5 false. Today's additions do not: `class_killer_int` replaced a density argument
("irrationals dense") with `exists_clear_step`, which uses no density input. That is worth checking
rather than assuming when the text is written.

### §4.5 Families in which Existence holds at once — cited by 6

Theorems 4.8 (ratio condition), 4.9 (wide gap), and consequences. All `[PROVED]`.

Bearing on it: Theorem 4.8 is what I re-derived independently today as a "ceiling check" without
recognising it. The census families are a large new class of the same kind.

### §6.8 Hard cases and incommensurate instances — cited by 5

A table of named arrangements with their cascades and instants, including the two irrational cases.

Bearing on it: `framework_cases_v1.py` now reproduces four of these exactly as a runnable harness, and
the day's measurements added the `R = 10.26` and `R = 10.31` readings for two of its rows.
**Q: does the harness get named here, or in §10?**

---

## The five open items

| | §, line | item | state |
|---|---|---|---|
| 1 | §2.3, 158 | **fitting between the AP locations** — how the fit feeds each runner's reading | untouched by today |
| 2 | §4.6, 319 | **the obligation in the gap frame** — the moving short gap misses both flanks at some instant | untouched. Note it already records that the "`u ≤ 7/8`" bound is the withdrawn first-window restriction |
| 3 | §6.7, 492 | **Existence** | reduced today to `CascadeCapped`, proved equivalent both ways. The item does not close; its statement gains an equivalent form |
| 4 | §8.2, 753 | **five differences at `n = 6…10`** | untouched |
| 5 | §8.2, 770 | **order 5 with four differences** | see below |

**Item 5 is the one with movement.** The manuscript records the largest `R` as `≈ 31/9` `[EMPIRICAL]`.
The order-5 certificate now proves `sup R = 31/9` by exhaustive word enumeration with exact rational
LPs, for ratio `S ≤ 26`. That is a **scoped** upgrade — `[PROVED for ratio ≤ 26]`, not unconditional, and
unbounded `S` stays open. **Q: is a ratio-bounded proof worth recording as a grade change, or does it
stay `[EMPIRICAL]` with the certificate cited?**

**Item 4's neighbouring paragraph already carries a pending ruling of yours.** §8.2 line 753 says of the
`n > 2k` row: *"whether this proof is native to the framework is the author's call, and nothing else is
built on it."* My finding today that `n > 2k` reduces to `k·(2/n) < 1` — the `k` in-the-way arcs cannot
cover the circle — is **evidence for that pending ruling, not a new issue.** The manuscript got there
first and left it for you. **Q: do you want to settle it in this update?**

---

## What the map says about tracing the edit

- Only two declarations are named in more than one section (`move`, `nextOpening`, both §6.1 and §7), so
  declaration-level coupling is loose; the coupling is section-level and concentrates on the five hubs.
- §7's counts are stale (records 9 modules / 161 theorems; the tree is 18 / 4,669) and §7 is cited by §5
  and §10, so a count change touches both.
- §10 cites six sections — it is the provenance hub, and the census's cross-repository provenance
  (`census_families_v1.json`, now committed here) belongs in its scope.

## The two standing risks, stated once

**Dropping.** Five open items, 5 `[OPEN]` grades, 10 `[VERIFIED]`, 4 `[DERIVED]`, 1 `[EMPIRICAL]`. The
map records each with a line number; a successor that loses one shows it as a diff. Re-running
`manuscript_map_v1.py` on v9.2 is the check, and it is mechanical.

**Importing.** The material most likely to carry an import is today's, because I wrote it and imported
four times while doing so. The specific candidates are named above: the `U`/`K` vocabulary, the word
"capped", and whether anything added falsifies §5's claim.
