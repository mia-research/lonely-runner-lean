# Retraction: `K` measures distance from the anchor, not difficulty

2026-09-11. Scripts `experiments/n8/ok_k_vs_hardness_v1.py`, `ok_k_hard_bigbox_v1.py`,
`ok_uncovered_examples_v1.py`. Exact `Fraction`.

I offered `E = (8, 807, 1083, 1239, 1454, 1931, 2491)` as "a speed arrangement the grid
reasoning does not cover", on the grounds that it needs `K = 39`. The example is wrong in
three independent ways, and the owner's challenge is upheld.

---

## 1. It is covered — by the first lemma in the chain  `[PROVED]`

`SMALL_DENOMINATOR_WITNESS_v1` §1: if `d ≤ 8` divides no speed, `t = a/d` is a witness.

| `d` | 2 | 3 | 4 | **5** | **6** | 7 | 8 |
|---|---|---|---|---|---|---|---|
| speeds divisible | 8, 1454 | 807,1083,1239 | 8 | **none** | **none** | 1239 | 8 |

`5` divides no speed, so `t = a/5` is a witness for all four `a`. Verified exactly: the
distances `‖e_j·(1/5)‖` are `2/5, 2/5, 2/5, 1/5, 1/5, 1/5, 1/5` — every one `≥ 1/8`. In the
grid language: **the 5-grid is complete** (`k(5) = 5 = m`, the audit's Arithmetic-Field
condition), site 0 is held only by the stationary runner because `0 ∉ {e mod 5} = {1,2,3,4}`,
and the nearest occupied site is `1/5 ≥ 1/8`. **Isolation on a grid — just not the 8-grid.**

I checked whether the tuple reaches the *8*-grid (it does not: `q | 8·gcd(E) = 8` forces
`t = p/8`, and the residues `[0,7,3,7,6,3,3]` fill only four sites) and never checked the
coarser grids, which is where the witness was.

## 2. It is the easiest instance in the session  `[VERIFIED — exact]`

| tuple | `\|G\|` | components | fraction of `(3/4)⁷ = 0.133484` |
|---|---|---|---|
| the `K = 39` tuple | `0.132969` | 1590 | **99.6%** |
| `E*` (true extremum) | `0.006387` | 8 | 4.8% |
| `T₁` (tight) | `0` | 4 | 0% |

Its good set is within `0.4%` of the no-correlation value. It needs a large `K` only because
`e₀ = 8` while `e_max = 2491` — a ratio of 311 — so an anchored walk in units of `1/e_max`
is long, through a good set that is in fact everywhere.

## 3. `K` is anti-correlated with difficulty  `[VERIFIED — exhaustive + sampled]`

Over the complete Case-2 enumeration of `[1..18]` (20 349 tuples):

- **`Spearman(K_min, |G|) = +0.4513`** — larger `K` goes with **larger** `|G|`, i.e. easier.
- Max `K` is **2** in *every* `|G|` band, including the hardest.
- The three hardest tuples (`|G| ≤ 2×` the minimum) — `(2,6,7,8,10,13,14)`,
  `(1,4,5,6,7,11,16)`, `(2,6,8,10,11,14,17)` — **all have `K = 1`**.

Sampled in larger boxes, the hardest decile keeps `K` small: max `K` = **1** at `[1..40]`,
**2** at `[1..90]`, **4** at `[1..200]`.

## 4. What the corrected statement is

`GRID_CERTIFICATE_v1` §4's caveat — "`K` unbounded a priori" — is true but was presented as
though it identified the gap. It does not. `K` grows on **easy** tuples, for a reason now
explicit (slow multiple of 8, fast remainder), and stays small on hard ones.

**I do not have an example of a genuinely hard arrangement the grid reasoning fails to
cover.** That is the honest position, and it is a stronger one than I stated. The open
question is correspondingly narrower: *is `K` bounded on tuples with small `|G|`?* — untested
outside the boxes above, and the right thing to attack next.

## 5. The process failure

Three checks would each have caught this before it was offered, and all three were available:
run the small-denominator lemma on the candidate (§1); compute `|G|` (§2); cross the statistic
against difficulty before calling it a difficulty statistic (§3). I ran none. The statistic was
adopted as a proxy for hardness without ever being validated as one — the **proxy-as-object**
failure named in `feedback_self_cert_words_audit_trigger`, and the object-level rule of
`CLAUDE.md` §2b: *every agent must name the object it tracks and check that object, never a
correlate.*

## 6. Ledger

`[RETRACTED]` the claim that `(8,807,…,2491)` is uncovered, and the framing of unbounded `K`
as the residual gap.
`[PROVED]` §1, the `d = 5` witness, verified by exact evaluation.
`[VERIFIED — exact]` §2's three `|G|` values.
`[VERIFIED — exhaustive]` §3's Spearman and band maxima over the complete `[1..18]` Case 2.
`[EMPIRICAL — sampled]` §3's larger-box rows.
`[STANDS]` the computation that this tuple never reaches the **8**-grid; and everything in
`CROWDING_DICHOTOMY_v1` and `GRID_CERTIFICATE_v1`, which this does not touch.

`n = 8` is **not proved.**
