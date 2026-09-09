# Where the proof can and cannot be: a map of the search

2026-09-10. **v2 — supersedes `WHERE_THE_PROOF_IS_v1.md`**, which floated the height
conjecture of §4 as untested. It has now been tested; see §4a. §1–§3 unchanged.

2026-09-10. Consolidates the ruled-out routes with the reason each fails, and states what
survives. Scripts `experiments/n8/ok_*.py`. Everything here is exact or exhaustive in a
stated box; nothing is asserted.

---

## 1. The one that would have been three lines — and is impossible  `[PROVED]`

> **Dream.** Find `φ ≥ 0` with `supp φ ⊆ [1/8,7/8]` and `φ̂(k) ≥ 0` for all `k`. Then
> `∫∏_j φ(e_jt)dt = Σ_{k·e=0} ∏_j φ̂(k_j) ≥ φ̂(0)⁷ > 0` — every term nonnegative — and a
> positive integral forces a `t` with every `e_jt ∈ [1/8,7/8]`. That is LRC(8), immediately.

**No such `φ` exists.** If `φ̂ ≥ 0` and `φ ≥ 0` then for every `t`,
`φ(0) = Σ_k φ̂(k) ≥ |Σ_k φ̂(k)e(kt)| = |φ(t)|`, so `φ(0) = max φ > 0` unless `φ ≡ 0`. But
`0 ∉ [1/8,7/8]`, so the support condition forces `φ(0) = 0`. ∎

**Consequence, and it is the useful one:** the negative terms in the ray series are
**structural**. They are not an artefact of taking `f` to be an indicator, and no choice of
test function removes them.

## 2. Optimising the test function does not help either  `[EMPIRICAL — measured]`

For `φ ≥ 0` on the arc, write `ratio = (absolute ray tail)/φ̂(0)⁷` at the extremal tuple
(supports 2–3, `|k| ≤ 60`; a *lower* bound on the true tail). `ratio < 1` would prove the
tuple.

| `φ` | `φ̂(0)` | `|φ̂(1)|/φ̂(0)` | ratio |
|---|---|---|---|
| **indicator on `[1/8,7/8]`** | 0.7501 | 0.3000 | **2.66** |
| `sin` | 0.4775 | 0.5657 | 1.75 |
| `sin²`, `sin⁴`, `sin⁸` | … | 0.686→0.882 | 4.99 → 36.97 |
| 3 bumps, width 0.10 → 0.02 | … | 0.313→**0.055** | 12.07 → **604** |

The arc spans 270°, so `0` lies in the convex hull of `{e(−t)}` over it and `φ̂(1) = 0` is
**achievable** — the three-bump weights are `1/(2+√2), 1/(2+√2), √2/(2+√2)` at
`t = 1/8, 1/2, 7/8`. But driving `|φ̂(1)|` down concentrates the mass and inflates every
other coefficient: the ratio moves the wrong way, monotonically, in every family tried.
**The indicator is the best test function found; local improvements backfire.**

## 3. The ruled-out list, with the reason for each  `[all PROVED or exhaustive]`

| route | why it fails |
|---|---|
| Bonferroni / moment truncation | `∫S₇ = 1/7` — all seven runners share a blocked residue on measure `1/7`, 290× independence. Every odd truncation negative. |
| **Signed** support truncation | totals alternate `+0.005, −0.156, +0.063` against a main term of `0.133`: larger than the main term, not decaying. |
| Absolute Fourier / ray bounds | supports 2–4 truncated already give `−0.46`; overshoot 3–4× for **every** tuple, easy ones included. |
| Pure positivity (`φ̂ ≥ 0`) | §1 — impossible. |
| Test-function optimisation | §2 — measured; best ratio 2.66. |
| `LRC(7)` / induction | gives existence on the circle, not **localisation** in the window; `LRC(2)` already hands over `[1/8,7/8]` and misses. |
| speed-floor finite reduction | adversarial dilate-plus-perturbation plateaus at `|G| ≈ 0.029` at **arbitrarily large** floors. |
| 3-body relaxation; pairwise `p ≥ 1/4` | settles 0.8% of tuples; `p ≥ 1/4` false (min `1/7`). |

The common cause is one number: the first-moment margin `8·(3/4)⁷ = 1.0679` turns positive
**exactly** at `n = 8`, and correlation eats 95% of it (`∫X = 0.0511` at the extremum). Soft
analytic methods have `6.8%` of room and need `95%`.

## 4. What survives, and the one concrete lead

**(B) the structural route.** `ov ≤ 4` covers **96.3%** of Case 2 with `min |G| = 0.014881`
— a 2.3× margin — and `ov ≥ 5` is **3.7%**, explicitly described (five speeds from `λT` for
one of three tight instances, plus two free), with the extremum identified and its base
`{1,3,4,5,7}` isolated. No method yet for the 96.3%.

**The lead.** Every dead route died on low-height resonances — small `∏_j|p_j|`. The ray law
gives `|R(p)| ≤ cap(s)/∏|p_j|`, so a tuple with **no** low-height resonance has a small tail
by construction. That suggests the right parameter is the Diophantine height

> `h(E) = min { ∏_j |p_j| : p ≠ 0 primitive, p·e = 0, no p_j ≡ 0 mod 4 }`,

and the conjecture `h(E) large ⟹ |G|` near `(3/4)⁷`. This is the classical
badly-approximable condition, it is exactly what "far from a tight instance" should mean
quantitatively, and it is directly testable against the `ov` statistic. **That is the next
thing to measure.**

## 4a. The height conjecture, tested — true but nearly vacuous  `[EMPIRICAL — exhaustive]`

`h(E) = min ∏|p_j|` over primitive resonances with no coordinate `≡ 0 mod 4`, computed over
supports 2 and 3 (so the figure is an **upper** bound on the true height — a support-4
all-`±1` resonance can have height 1). Over all 20 349 Case-2 tuples in `[1..18]`:

| `h(E)` | tuples | `min |G|` | mean `|G|` |
|---|---|---|---|
| 1 | 19 963 (**98.1%**) | `0.006387` ← global min | 0.1098 |
| 2 | 386 (1.9%) | **`0.080118`** | 0.1430 |

**The direction is right and the leverage is not there.** `h > 1` gives
`|G| ≥ 0.080118` — **12.5× the target**, and `0.60` of `(3/4)⁷` — a genuinely strong bound.
But `h = 1` holds for **98.1%** of tuples, because `∏|p_j| = 1` means all coordinates `±1`,
i.e. a three-term relation `e_i + e_j = e_k`, which is generic. So `h` collapses to the
relation-count-`0` condition already recorded in `RELATION_DICHOTOMY_v1`, and separates
2–6% of tuples depending on the box. **It is not new leverage.**

What the test does establish: the mechanism is confirmed — low-height resonances are exactly
what destroys `|G|` — so the useful parameter must be the **height profile** (how many
resonances at each height), not the minimum. That is what the relation count was already
measuring, and `ov` measures better.

## 5. Grades

§1: **PROVED** (three lines, elementary). §2: **EMPIRICAL** — measured over the families
tried, with truncated tails; it shows those families fail, not that no `φ` works. §3: each
entry **PROVED by counterexample** or **exhaustive** in its stated box, as recorded in the
source documents. §4: the `ov` figures are **exhaustive over `[1..24]`**. §4a: **EMPIRICAL**, exhaustive over
`[1..18]` with the support-2/3 caveat; the conjecture is **CONFIRMED in direction but
REJECTED as a dichotomy** — `h = 1` is generic at 98.1%.
