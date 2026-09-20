# Check of `HANDOVER_2026_09_12` — v2, with corrected figures and a bug in the shared artifact

2026-09-12. Supersedes `HANDOVER_CHECK_2026_09_12_v1`. **Every `max-min-gap` figure in v1 was
wrong**, because the artifact they came from computes that quantity on the wrong candidate set.
The verdicts are unchanged. `n = |V|` is stated for every row.

---

## 1. The bug in `experiments/lrc_adjoin_vs_translate_v1.py`  `[FIXED]`

`brute_force` built candidate times as `t = (k ± 1/n)/d` over **unsigned** pairwise differences
`d`. Those are the BSM boundary times — where some pair's gap equals the threshold. They are
event-complete for the **predicate** ("is there a `t` with min-gap ≥ 1/n"), which is what BSM
proves, so **every verdict the script has ever returned is sound**.

They are **not** complete for the **maximum** of the min-gap. The min-gap is a minimum of linear
functions, hence concave on each cyclic-order cell, so its maximum can sit strictly inside a
cell; probing BSM points and their midpoints does not find it. The script nevertheless printed
a `max-min-gap` figure computed over that set, and the figure is an underestimate whenever the
maximum is interior.

**This is the exact error recorded in [[feedback_count_the_runners_given_2026_09_12]].** That
memory states the corrected value for `{0,2,4,6,104}` — `10/53` at `t = 5/53`, not `49/260` —
but **the fix was never applied to the code**. The script still emitted `49/260`. The memory
documented the trap while the artifact it names kept reproducing it, and it caught two sessions
today.

Fix: `_extremal_candidates()` generates `t = m/Δ` for `Δ` a **signed** difference of signed
differences; the predicate still comes from the BSM set; an assertion requires the two routes to
agree on the verdict.

| check | before | after | expected |
|---|---|---|---|
| `{0,2,4,6,104}` | `49/260` | **`10/53` at `t = 5/53`** | memory's corrected value ✓ |
| `(2,6,7,8,10,13,14)` | `3/28` | **`1/9` at `t = 5/9`** | independently confirmed ✓ |
| control: AP `(1..8)` | — | **True, `1/8` at `t = 1/8`** | uniform 8-grid ✓ |

## 2. Corrected table  `[VERIFIED — patched artifact, two routes agreeing]`

| set | `n` | residues mod `n` | complete | global isolation | max-min-gap vs `1/n` |
|---|---|---|---|---|---|
| `(1,2,3,4)` | 4 | `[1,2,3,0]` | yes | **True** | `1/4` = `1/4`, `t = 1/4` |
| `(1,2,3,8)` | 4 | `[1,2,3,0]` | yes | **True** | `1/4` = `1/4`, `t = 1/4` |
| `(2,4,6,104)` | 4 | `[1,2,3,0]` (after `/g`, `g=2`) | yes | **True** | `1/4` = `1/4`, `t = 1/8` |
| `(2,6,7,8,10,13,14)` | 7 | `{0,1,4,5,6}` | **no** | **False** | **`1/9`** < `1/7` |
| same, `0` adjoined | 8 | `{0,2,5,6,7}` | **no** | **False** | **`1/9`** < `1/8` |
| AP `(1,…,8)` | 8 | `0..7` | yes | **True** | `1/8` = `1/8`, `t = 1/8` |

v1 reported `3/28` and `23/208` in rows 4 and 5. Both were the buggy figure. v1 §6 also called
`23/208` "the correct value" while criticising an earlier pass of mine — that sentence is
retracted; `23/208` was not correct either.

## 3. Presentation — do not display the translated form

v1 wrote `(1,2,3,8)` as its reduced form `(0,1,2,7)`. They are the same four runners, but
printing the translated form puts a runner at `0` on screen and invites reading a free
translation as an adjoined stationary runner — operation (A) mistaken for operation (B).

The criterion needs no zero. Divide by `g` = gcd of the pairwise differences, then take
residues mod `n` of the speeds **as given**; completeness is translation-invariant, since
shifting every speed by `c` permutes the residues.

## 4. The modulus — conclusion reinstated, evidence withdrawn

v1 claimed `HANDOVER:21` ("the modulus belongs to the AP, not to `n`") is false, on two
supports. One was a strawman and is withdrawn: it tested "complete residue system mod span",
which with `n` runners and span > `n` is false **by counting**, before any mathematics — all 94
of its "disagreements" were exactly the 94 isolating sets with span > 4. A statistic that cannot
come out otherwise is not evidence.

**The conclusion stands on the other support**, which is arithmetic, not a test: `n` gaps
summing to 1 with each ≥ `1/n` forces each to equal `1/n`, so the positions are the uniform
`n`-grid and the criterion is complete residues mod `n`. Refuting my own mechanism does not
refute the thesis; v1's blanket withdrawal over-corrected.

Independent support, against a **satisfiable** criterion: complete residues mod `n` ⟺ global
isolation over all 658 primitive 4-subsets of `[0..12]` (104 isolate), **0 disagreements**.

`(1,2,3,8)` is the clean witness: drawn from the AP `1..8`, it isolates, and its residues are
complete mod 4 and not mod 8. Being drawn from an AP of length `m` does not confer modulus `m`;
the AP `1..14` needs mod 14 because it *has* fourteen runners.

## 5. Status

`[FIXED]` §1's extremal-candidate bug in `experiments/lrc_adjoin_vs_translate_v1.py`.
`[VERIFIED — two routes agreeing]` §2's table.
`[RETRACTED]` v1's `3/28`, `23/208`, `39/322`, `508501/4810121`; v1 §6's claim that `23/208`
was correct; and v1 §4's 94-disagreement test.
`[STANDS]` v1's two findings on the handover: `(2,6,7,8,10,13,14)` is not a grid and does not
globally isolate; and the modulus is `n`. Both independently confirmed by the owner.
`[OWED]` The `(8,807,…,2491)` max-min-gap figures were not recomputed — the signed
difference-of-differences set is large there. Their **verdicts** stand on the residue criterion,
which is proved.

**n = 8 is not proved; nothing here bears on it.**
