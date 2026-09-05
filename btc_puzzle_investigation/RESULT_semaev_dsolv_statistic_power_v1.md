# RESULT — Semaev point-decomposition: the `d_solv` statistic's POWER, and what it does to R1

**Date 2026-08-05.** Target B (R1, the prime-field-native Semaev index-calculus lever named in
`ANALYSIS_n4_cover_family_indexcalculus_v2.md`). Probes (scratchpad, exact over GF(p), no float):
`probe_dsolv_power_v1.py`, `probe_consistent_repro_v1.py`, reusing the harness
`semaev_elimination_v1.py` (`measure_system`, `decomposable_target`). Scope: `p=211`, `m∈{3,4}`,
`|V|∈{2,3,4,5}`. **These were VALIDATION + REPRODUCTION probes, not a pre-registered graded test**;
the graded follow-up (§4) is pre-registration-owed.

## 1. Finding 1 — the prior R1 "clean comparison" statistic is BLIND `[PROVED-mechanical, reproduced]`

`RESULT_semaev_cm_lever_v1.md` leaned on the **matched inconsistent** arm (`matched_curves_compare`)
as "the clean comparison" for a CM solving-degree lever. That arm's `d_solv` is **forced
curve-independent**:
- Measured `d_solv == Dmax == deg(Sx) + m(|V|−1)` exactly, **identical** for secp_j0 / nonCM /
  j1728, at `m=3, |V|=2,3,4` (15,18,21). **Stable when `Dmax` is raised by 8** ⇒ genuine resolution
  at that degree, not a None-cap artifact.
- `deg(Sx)` is proved curve-independent (isobaric leading form), so the inconsistent-regime solving
  degree = a curve-independent combinatorial ceiling. **"Identical across curves" is therefore
  forced, and carries zero power to detect a CM lever.**
- (At `m=4,|V|=2` the arm returns `d_solv=None` — the search cap `Dmax=21 < deg(Sx)+m(|V|−1)=36`;
  unresolved, also uninformative.)

**Firing control** (does `d_solv` have power at all?): on planted early-resolving systems it fires —
`{x1−5,x2−7,x3−11}` and `{x1²−2,x2−x1,x3−1}` both give `d_solv=1`. (A planted-inconsistent system
with an unbounded variable returns None — a Macaulay-truncation edge effect, noted, not a real
inconsistency.) So the statistic is not globally blind; it is blind **specifically in the
inconsistent, all-variables-bounded Semaev regime**, where it saturates the ceiling.

⇒ **The prior grade overstates.** Re-scope: the isobaric leading-form curve-independence stays `[PROVED, all m]` (the first-fall-DEGREE curve-independence it implies is `[HEURISTIC+CITED]`, `[VERIFIED]` at scope — the isobaric fact does not upgrade it);
the *inconsistent-regime* matched solving degree is `[FORCED curve-independent — no power]`; the
*consistent-regime* (attack-relevant) solving degree was measured only **unmatched** (per-curve
targets), so the CM-lever question there was **not cleanly answered**.

## 2. Finding 2 — the secp-SPECIFIC consistent-regime candidate DISSOLVES `[EMPIRICAL, reproduced]`

A single draw (`seed=1, m=3, |V|=4`) showed secp with `quo=12, d_solv=19` vs `6, 20` for both
controls — a candidate secp lever (more decompositions, lower solving degree). **Reproduction over
K=15 matched-by-seed draws kills the secp-specificity:** secp exceeds *both* controls in only
**3/15** (`|V|=4`), **0/15** (`|V|=3`), **5/15** (`|V|=5`) draws, and **j1728 (the other CM curve)
matches or exceeds secp**. The seed-1 standout was a single-draw target confound.

## 3. Finding 3 — a generic-CM decomposition-count effect (dissolution into a sharper pattern) `[EMPIRICAL, suggestive, CONFOUNDED]`

The non-CM curve's decomposition count concentrates at `quo=6 (=3!)`; **both** CM curves carry a
right-tail of higher `quo`, growing with `|V|`. Draws with `quo>6` (of 15):

| `|V|` | nonCM | secp_j0 (μ₆) | j1728 (μ₄) |
|---|---|---|---|
| 3 | 0 | 1 | 6 |
| 4 | 1 | 5 | 8 |
| 5 | 3 | 8 | 13 |

- **Hypothesis (unproved):** extra decompositions from automorphism-image coincidences (CM curves
  have μ₄/μ₆ vs non-CM μ₂), more likely as the factor base grows. `quo` = number of relations an
  index-calculus attacker gets per target, so *more decompositions per target* is an
  index-calculus-relevant structural difference — **worth characterizing.**
- **Why it is NOT (yet) a lever:** (a) not secp-specific — j1728 shows it at least as strongly;
  (b) it does **not** systematically lower `d_solv` (secp `d_solv<`both controls only 0–5/15; the
  ceiling barely moves); (c) **confounded** — the three curves have different group orders at
  `p=211`, which alone changes decomposition counts; (d) `p=211, m=3` — no scale power (banner).

## 4. Disposition + owed follow-up

- **Record against R1 / the prior:** `RESULT_semaev_cm_lever_v1.md`'s "no CM solving-degree lever
  `[VERIFIED, p≤307, m≤4]`" is **re-scoped by Finding 1** — its matched arm was blind; keep only the
  isobaric leading-form fact `[PROVED, all m]` (first-fall-DEGREE curve-independence `[HEURISTIC+CITED]`)
  and mark the solving-degree CM-lever question **OPEN** (matched
  consistent-regime comparison never run).
- **B's shape changed.** The original B ("push d_solv to `m≥5`") is de-prioritized: (i) `m=5` (S₆)
  build is intractable in the current harness (experiment-designer probe: S₆ did not build in 240s);
  (ii) the inconsistent-regime `d_solv` there would be forced anyway (Finding 1). The **real** B is a
  **pre-registered, matched consistent-regime comparison** that (a) matches or controls for group
  order, (b) uses `quo` (relation yield) and consistent-regime `d_solv` as statistics, (c) tests the
  Finding-3 CM decomposition-count effect and whether it yields any relation-collection advantage,
  (d) carries a firing control that fires in the *consistent* regime. → experiment-designer.
- **Update 2026-08-05 (grounding, `PREREG_cm_decomposition_count_PROVISIONAL_v1.md`):** at `p=211` the
  j1728 arm `y²=x³+3x` is **supersingular** (`|E|=p+1`, μ₄ not rational at `p≡3 mod 4`), NOT a μ₄-CM
  ordinary control — so Finding 2's "j1728 shows it too" is confounded by supersingularity, and Finding 3
  needs an `|E|`-matched *ordinary* design at `p≡1 mod 12`. Does not overturn Finding 1 (statistic
  blindness) nor that secp alone did not systematically exceed the non-CM control.
- **Grades:** Finding 1 `[PROVED-mechanical]`; Finding 2 `[EMPIRICAL — secp-specificity refuted,
  reproduced]`; Finding 3 `[EMPIRICAL — suggestive, confounded, pre-registration owed]`. No lever
  claimed; no closure claimed.
- Master-v5 reconciliation (with N4 `ANALYSIS v2`) remains owed, compile-diff-gated.
- Cross-links: `ANALYSIS_n4_cover_family_indexcalculus_v2.md` (R1), `RESULT_semaev_cm_lever_v1.md`.
