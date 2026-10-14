# Audit of P3 and P4, and the enumeration extended

2026-09-12. Owner flagged P3/P4 of `PROOF_CANDIDATE_v3.md` as unverified. This note gives
the proofs, stress-tests them, and states where P4 has no content.

## 1. P3 — components are short  `[PROVED]`

`G_D = { t : ‖dt‖ ≥ 1/8 ∀d ∈ D }` and `d_max = max D`.

`G_D ⊆ G_{d_max}`, since `G_D` imposes `d_max`'s condition among others. The bad set of a
single `d` is the union of `(j/d − 1/(8d), j/d + 1/(8d))` over `j`, each of width `1/(4d)`.
Consecutive bad intervals are `1/d` apart, so the good gap between them has length
`1/d − 1/(4d) = 3/(4d)`.

Every component of `G_D` lies inside one component of `G_{d_max}`, hence

> every component of `G_D` has length `≤ 3/(4 d_max)`. ∎

## 2. P4 — the count bound  `[PROVED]`

`|G_D| = Σ(component lengths) ≤ count × max component length ≤ count × 3/(4 d_max)`. So

> **count ≥ (4 d_max / 3) · |G_D|.** ∎

## 3. Stress test  `[VERIFIED]`

Adversarial cases — the three tight instances, all-odd sets, minimum span, very large
`d_max`, the pinned minimiser, E*:

| case | `d_max` | count | `|G_D|` | P4 bound | P3 | P4 |
|---|---|---|---|---|---|---|
| tight `(1,2,3,4,5,6,7)` | 7 | 4 | 0 | 0 | ok | ok |
| tight `(1,2,3,4,5,7,12)` | 12 | 4 | 0 | 0 | ok | ok |
| tight `(1,4,5,6,7,11,13)` | 13 | 4 | 0 | 0 | ok | ok |
| all odd `(1,3,5,7,9,11,13)` | 13 | 9 | 0.1136 | 1.97 | ok | ok |
| pinned minimiser `(1,2,3,4,5,7,8)` | 8 | 2 | 0.0286 | 0.30 | ok | ok |
| E* runner 0 | 14 | 8 | 0.0064 | 0.12 | ok | ok |
| `(1,2,3,4,5,6,100000)` | 100000 | **8752** | 0.0656 | **8750.0** | ok | ok |
| `(1,2,3,4,5,7,99991)` | 99991 | **2862** | 0.0214 | **2856.8** | ok | ok |

Random stress, 5,975 primitive sets drawn from boxes `[1..9]` through `[1..600]`
(121 of them measure-zero): **P3 violations 0, P4 violations 0.**

P4 is close to exact at large `d_max` — 8750 against 8752, 2856.8 against 2862.

## 4. Where P4 has no content  `[VERIFIED]`

P4 cannot exclude count 2 unless its bound exceeds 2. Over 2,994 primitive sets sampled from
boxes up to `[1..38]`:

> **1,771 of 2,994 (59.2%) have P4 bound < 3.**

At the tight instances the bound is literally `0`. So **P4 proves nothing on its own** — it is
strong exactly where enumeration cannot reach (large span) and silent exactly where
enumeration can (small span). The measure lemma of `PROOF_CANDIDATE_v3` §4 is what gives it
content; without it P4 is an identity with no consequence.

## 5. Enumeration extended

All 7-element primitive difference sets in a box — every 8-set of that span from one runner's
view. Method: float screen keeping anything with float-count ≤ 8, then exact `Fraction`
verification of survivors.

| `N` | primitive sets | screened | exact min count |
|---|---|---|---|
| 16 | 11,440 | — | 2 |
| 20 | 77,400 | — | 2 |
| 22 | 170,213 | — | 2 |
| 24 | 345,304 | 2,025 | 2 |
| 28 | **1,180,572** | 2,303 | **2** |

Minimisers at `N = 28`: `(1,2,3,4,5,7,8)`, `(1,2,3,4,5,7,16)`, `(1,3,4,5,6,7,8)`,
`(1,3,4,5,6,7,16)`, `(1,3,4,5,6,8,14)`, `(1,3,4,5,7,8,12)`. Never 0, never 1.

**Screen control.** Re-running `N = 24` through the screened pipeline reproduces the exact
run identically — same 345,304 sets, same minimum 2, same minimisers — so the screen is not
dropping low-count candidates. A float screen can only *under*-count (single-point components
vanish), which errs toward keeping candidates, not discarding them.

`N = 38` (12,620,256 sets) is running.

## 6. Status

`[PROVED]` P3, P4 — §1 and §2.
`[VERIFIED]` §3's stress test, 5,975 sets, 0 violations; §5's boxes to 1,180,572 sets;
the `N = 24` screen control.
`[RECORDED]` §4 — P4 is vacuous on 59.2% of small-span sets and at every tight instance.

n = 8 is **not proved**. P3 and P4 are sound but carry no weight without the measure lemma.
