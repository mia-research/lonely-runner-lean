# Why isolation occurs in the remaining 19.1%, and the Lean audit

2026-09-21, version 1. Two things the owner asked: why isolation happens in what is left and
what distinguishes it from the proved part, and confirmation that every proof is in Lean.

Artefacts: `experiments/nN/n5_why_residue_v1.{py,out}` · `n5_equidist_v1.{py,out}` ·
`experiments/n8/full_audit_v1.{lean,out}` · `LonelyRunner/LRC/Spec/WindowN.lean` (new)

---

## 1. Lean audit  `[COMPLETE — 130 declarations, all axiom-clean]`

| file | declarations | what it carries |
|---|---|---|
| `DoorsN.lean` | 94 | the whole `n = 8` Spec layer at every `n`; `doors_agree` |
| `FlankFiniteN.lean` | 15 | decidable predicate, bridge, P2, P3, scaling, the gap criterion |
| `ResonanceN.lean` | 16 | resonance, `resonant_iff_dvd_of_prime`, **P1′** (both halves) |
| `WindowN.lean` | **5 (new)** | **P4**, the sharp-window criterion, with a worked instance |

**130 of 130 axiom-clean** (`[propext, Classical.choice, Quot.sound]` or fewer). **No `sorry`,
no `native_decide`, no `admit`** anywhere — the only textual hits are prose in docstrings.

**P4 was the gap and it is now closed.** `windowOK n L x w` is a decidable rational certificate:
for each `d`, the image `[d·x, d·(x+w)]` must fit inside one band `[k + 1/n, k + 1 − 1/n]`.
Proved: `lonely_of_windowOK` (the certificate governs the whole window) and
`flank_of_windowOK` / `lonely_flank_of_windowOK` (a certified window wider than `1/e` forces a
lonely opening of the flank). Demonstrated non-vacuous on `ds = (1,2,5,16)` — a residue set that
P1′, P2 and P3 all miss — with window `(6/25, 9/25)` of width `3/25 > 1/16`.

**Still not in Lean:** P5, the self-similar scaling reduction, and the five-triple statement.
Those remain measured only.

---

## 2. Why isolation occurs in the residue

Comparing the residue with the proved part, over primitive card-4 sets to `[1,34]`:

| | proved (35,077) | residue (8,578) |
|---|---|---|
| mean `|L|` | 0.2119 | **0.2095** |
| mean components of `L` | 14.76 | **13.78** |
| mean largest interval `W` | 0.0301 | 0.0264 |
| mean `W·e` | 0.801 | 0.726 |
| mean openings | 6.54 | **6.18** |
| mean `e` | 27.8 | 28.4 |

> **The residue is not structurally different.** Every measure matches to within a few percent.

And `|L| ≈ 0.21 ≈ (3/5)³` — exactly the value for three independent blockers each removing `2/5`
of the circle. Isolation occurs because **the openings equidistribute in the lonely set**:

> **#openings ≈ `|L| · e`** — predicted `0.2095 × 28.4 = 5.95`, observed **6.18**.

That is the whole mechanism. Nothing special is happening in the residue; the lonely set has its
usual fifth of the circle and the `e` openings find their usual share of it.

---

## 3. So what *is* different about it

Not the sets — the **tools**.

| criterion | what it does |
|---|---|
| P1′ | **names a point**: `a = e·s`, or `a = k·e + 1` |
| P2 | **names a point**: the last opening `j = e − 1` |
| P3 | exhaustion below 15 |
| P4 | **finds a wide interval**: `W > 1/e` |

Every one of them either names a single instant or requires one component of `L` to be wide. The
residue is precisely the set of cases where **no named instant lands in `L` and no component is
wider than the opening spacing** — an accident of position, not a different phenomenon.

That is why the width-based criteria plateau near 81%: they are answering the wrong question.

---

## 4. The shape the residue actually needs

A **counting** argument, not a width one. Writing `D = #openings − |L|·e` for the discrepancy
(`n5_equidist_v1.out`, 10,975 sets):

| | value |
|---|---|
| mean `D` | +0.210 |
| min `D` | **−2.959** |
| min `|L|` over the class | **0.1000**, at `(5,15,20,21)` |

`#openings ≥ |L|·e − D`, so a floor on `|L|` plus a bound on `D` gives openings outright:
with `|L| ≥ 0.10` and `D ≥ −2.96`, `#openings ≥ 1` once `e ≥ 39.6`, leaving a finite check below.

**Two cautions, both measured.** `D` is not constant — its minimum drifts `−1.665, −2.400,
−2.788, −2.959` across `e` buckets 15, 20, 25, 30, so a uniform bound is not yet in evidence.
And the trivial discrepancy bound (an arithmetic progression against a union of `k` intervals
errs by at most `k`) gives `D ≤ 14` here, which would need `e ≥ 150` — far too loose against an
observed 2.96. A real discrepancy estimate is required, not the trivial one.

The minimum `|L| = 0.10` is attained at `(5,15,20,21)` — the self-similar case, which §4 of
`N5_WHITTLE_v1.md` already closes. So the floor on `|L|` for the *rest* of the residue is higher.

---

## 5. Grades

| claim | grade |
|---|---|
| 130 declarations, all axiom-clean, no `sorry`/`native_decide` | `[PROVED — full_audit_v1.out]` |
| P4 formalised as a decidable certificate | `[PROVED — WindowN.lean]` |
| P4 non-vacuous on a residue set | `[PROVED — `(1,2,5,16)`, window `(6/25, 9/25)`]` |
| residue and proved part structurally indistinguishable | `[VERIFIED — six measures, all within a few percent]` |
| `#openings ≈ |L|·e`, `|L| ≈ (3/5)³` | `[VERIFIED — predicted 5.95, observed 6.18]` |
| `|L| ≥ 0.10` on the class | `[VERIFIED — exhaustive to [1,34]]` |
| `D` bounded uniformly | **not established** — the minimum drifts with `e` |
| P5 in Lean | **not done** |
| the residue | **not proved** |
