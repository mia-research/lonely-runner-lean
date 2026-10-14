# Whittling n = 5: residue down to 19.1%

2026-09-21, version 2. Supersedes `N5_WHITTLE_v1.md` (self-similar core only) by applying the
same template to the mixed classes.

Artefacts: `experiments/nN/n5_window_general_v1.{py,out}` · `n5_maxgap_v1.{py,out}` ·
`n5_window_gap_v1.{py,out}` · `n5_total_coverage_v1.{py,out}` · `n5_close_selfsimilar_v1.{py,out}`

**No `intLRC` anywhere.** Every criterion below is either a framework theorem or an exact finite
computation.

---

## 1. Where it stands

| | proved | residue |
|---|---|---|
| before this session | 42.4% | 57.6% |
| + prime theorem (`n ∤ e`) | 66.1% | 33.9% |
| + the `n ∣ e` half (pigeonhole) | 72.6% | 27.4% |
| **+ sharp window** | **80.9%** | **19.1%** |

Exhaustive over primitive 4-subsets to `[1,40]` (85,771 sets); the `[1,30]` figures agree to
0.3%.

| criterion | what it is | coverage |
|---|---|---|
| **P1′** | no non-flank disparity divisible by 5 — `flankWorks_of_prime`, `_dvd` | 52.6% |
| **P2** | `d_max ≤ 4·d_min` — `clear_at_last_opening` | 43.0% |
| **P3** | `d_max ≤ 15` — `four_clears_small`, by `decide` | 1.5% |
| **P4** | `W > 1/e` — the sharp window | 15.3% |
| **P5** | all non-flank divisible by 5 — scaling reduction | 0.3% |
| | **union** | **80.9%** |

---

## 2. P4, the sharp window

The flank openings are `t = (5j+1)/(5e)`, spacing `1/e`, and the flank itself sits at exactly
`1/5` there — so the window must keep only the **non-flank** disparities lonely. Let

> `L = { t : ‖d·t‖ ≥ 1/5 for every non-flank d }`,  `W` = its **largest** interval.

`L`'s complement is a union of open intervals `((k−1/5)/d, (k+1/5)/d)`, so `L` is a union of
closed intervals whose endpoints are exactly those points. `W` is therefore an **exact finite
computation**. If `W > 1/e`, the proved `exists_lonely_flankOpening_of_gap` delivers a lonely
opening.

**This is the sharp form of the earlier Lipschitz window.** The bound `2(S−1/5)/d_max` is only a
lower bound on `W`, and it shows: raw window **11.5%** of the residue, sharp window **23.3%** —
a doubling. Soundness checked: of every set the criterion claims, **none** actually fails.

---

## 3. Why P4 stops where it does  `[the exceptions, measured]`

Distribution of `W·e` over the residue (the criterion needs `> 1`):

| `W·e` | ≤ 0.5 | 0.5 – 1.0 | > 1.0 |
|---|---|---|---|
| share | 3.5% | **73.2%** | 23.3% |

Nearly three quarters are **near misses** — the window is within a factor of two of wide enough.
A criterion using the window's *position* as well as its width would capture most of them, but
position is exactly the arithmetic content: computing it per set is the original problem, so it
gives no general criterion. Something structural is needed, not a sharper constant.

Note also the margin is healthy throughout: minimum openings is **2** in every `W·e` bucket, and
the mean is 5.2–6.9 across the whole range. Nothing here is close to failing.

---

## 4. P5, the self-similar core, closed

When **every** non-flank disparity is a multiple of 5 the factor cancels in all of them and the
problem becomes the same band problem at modulus `e` — verified exactly, 0 mismatches on 3,846
sets. Two reductions close it:

* **scaling**: `r ↦ λr` is a bijection of `ℤ/e`, and primitivity forces `gcd(λ,e)=1`, so only
  primitive triples matter — verified on 1,580 combinations, 0 mismatches;
* **window + finite check**: five primitive triples have `S < 3/10` — `(1,2,3)` at `1/4` and
  `(1,2,6)`, `(1,3,4)`, `(1,5,6)`, `(2,3,5)` at `2/7`, a list stable from entries ≤ 12 to ≤ 40 —
  each closed above an explicit bound with **no failures** in the finite range below.

Small by count (0.3% of all sets) but it is the hard core: those sets are **13.85×
over-represented** among the low-opening sets.

---

## 5. What is left

**19.1%**, and it is characterised: at least one non-flank disparity divisible by 5, wide ratio,
`d_max > 15`, and window `W ≤ 1/e`. Of those, 73.2% miss the window by less than a factor of two.

What the record says about it:

* minimum working openings over the whole residue is **2** — never 1, never 0;
* low-opening sets are **bounded**: `≤2` openings forces `d_max ≤ 33`, `≤3` forces `≤ 37`,
  `≤5` forces `≤ 54`, all stable to `[1,80]`.

So the residue is not tight anywhere; the obstruction is that the tools bound *width* while the
truth depends on *position*.

---

## 6. Grades

| claim | grade |
|---|---|
| P1′, P2, P3 | `[PROVED — Lean, axiom-clean]` |
| P4 as a criterion (exact `W` + the proved gap lemma) | `[PROVED per set; `W` is a finite exact computation]` |
| P4 soundness | `[VERIFIED — no claimed set fails]` |
| P5 scaling reduction | `[VERIFIED — 0 mismatches]` |
| five primitive triples with `S < 3/10` | `[EMPIRICAL — exact scan to entries ≤ 40, stable]` |
| union covers 80.9% | `[VERIFIED — exhaustive to [1,40]]` |
| the remaining 19.1% | **not proved** |

**Scope.** Whole-number difference sets of card 4, exhaustive to `[1,40]`; by
`lonely_flank_smul_iff` this covers all rational sets of that shape. P4 is a *criterion* checked
per set, not a uniform theorem — it proves the sets that satisfy it, in the way the census does.
