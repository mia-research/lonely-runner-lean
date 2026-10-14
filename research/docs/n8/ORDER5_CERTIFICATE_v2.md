# Order 5: the finite certificate, margin realisability, and what the ratio sweep shows

2026-09-16. Supersedes `ORDER5_CERTIFICATE_v1.md` (S ≤ 6). Everything v1 established is carried forward; two things in it
are **corrected** by the wider sweep, and they are marked `[CORRECTS v1]` where they appear.

Scripts: `experiments/n8/order5_certificate_v3.py` (exact rational simplex; outputs `order5_certificate_S<N>_v3.out`),
`order5_certificate_v2.py` (vertex enumeration, kept as the independent check), `order5_cross_shift_v1.py` / `_v2.py`.


**Notation, corrected.** Throughout this document `S = d_max/d_min` is the subject's **ratio** of largest to smallest
difference, as the manuscript defines it (§ Notation). The manuscript reserves the word **spread** for `W = v_8 − v_1`, the
spread of the speeds, which is a different quantity — a difference, not a ratio. `ORDER5_CERTIFICATE_v1.md` and this
document's own first draft called `S` "the spread"; that re-collided two symbols which audit finding C1 had already
separated (manuscript v9.1). The mathematics was never affected — every result here is about `d_max/d_min` — but the word
is wrong in v1 and is corrected here.

---

## 1. What makes the problem finite  `[unchanged from v1]`

Suppose the cascade reaches `R = 4` and take the **first** step at which it does. Every earlier step has `R < 4`, and after a
setting of `x` at lap `Q` the value is exactly `R = (5Q + 1)/s_x` (`ORDER5_GROWTH_v2` §2). Hence, for an arrangement of ratio
`S = d_max/d_min`:

- **the nearest runner never sets** before the exceedance — its reading is 1, so its first setting would give `R = 6`;
- **every lap is bounded**: at the step before the exceedance `R < 4`, so `Q < (4S + 1)/5`;
- **laps strictly increase per runner**, so each of the three other runners sets at most `L = ⌊(4S−1)/5⌋` times, and the whole
  word has at most `3L` moves.

Finitely many words `(setter, lap)`; each word's conditions are linear in the readings once cleared of denominators:

    | u_{x_j}(Q_{j-1} + 1/5) − Q_j·u_{x_{j-1}} | < u_{x_{j-1}}/5      (the setter is in the way just before it sets)
    (Q_j + 1/5)·u_{x_{j-1}} > (Q_{j-1} + 1/5)·u_{x_j}                 (the instant advances)

with `sup R = (5Q_M + 1)/min u_{x_M}` over the word's polyhedron. These are necessary conditions only — "the setter has the
latest opening" and "the others are clear" are dropped — so the optimum **bounds the true one from above**, the direction a
proof of `R < 4` needs.

## 2. The boundary discipline is load-bearing  `[the 4.125 value, sharpened from v1]`

With the inequalities taken closed — that is `experiments/n8/order5_certificate_v1.py`, kept because its answer is instructive,
output `order5_certificate_S6_v1.out` — the enumeration returns `sup R = 33/8 = 4.125` on the word `(1,1), (2,1), (1,2), (3,1)`,
the same 4.125 the earlier floating-point linear programs hit (status v6 §3). It is an all-boundary configuration, which the
Boundary Set Method counts as **clear**: zones are open (§1.2 of the manuscript), so a runner sitting exactly on a zone edge is
not in the way and never sets.

Stated precisely, because the loose version invites a wrong repair: the closed LP is a **valid relaxation whose bound is too
weak**, not a false computation. Its feasible set is a superset of the realisable one, so `4.125` is a true upper bound over
that superset — it simply sits above the cap and therefore proves nothing. What is not realisable is the **word**: it carries
`max τ = 0` exactly. So 4.125 is not evidence against the cap, and a closed relaxation elsewhere in the programme is not
thereby an error to be "fixed".

Enforcing strictness removes it: each condition is tightened by a margin `τ`, a word counts only if `max τ > 0`, and the
optimum is taken on the closure. The 4.125 word has `max τ = 0` and is discarded.

## 3. Margin realisability: the two optima are joint, not sequential

`ORDER5_GROWTH_v2.md` §10 is why this section exists: uniform-constant pricing was refuted there by the constants themselves,
leaving the joint structure as the only remaining route. What follows is that structure, stated so it can be checked.

The certificate solves two linear programs per word, and it matters that they are two readings of **one** polytope rather than
a chain of two arguments. State it properly.

For a word `w` let

    P(w) = { (u₂,u₃,u₄,τ) : every condition tightened by τ holds, 1 ≤ u_i ≤ S, 0 ≤ τ ≤ 1 },

a convex polytope. Put `τ*(w) = max{ τ : (u,τ) ∈ P(w) }` (the **margin threshold**) and, on its `τ = 0` face,
`m*(w) = min{ u_{x_M} : (u,0) ∈ P(w) }` (the **minimal final reading**). The word is realisable exactly when `τ*(w) > 0`, and a
configuration realises it with margin `ε` when `τ ≥ ε`.

> **Lemma (margin realisability).** If `τ*(w) > 0` then
> `inf{ u_{x_M} : (u,τ) ∈ P(w), τ > 0 } = m*(w)`,
> so the supremum of `R` over **strictly realisable** configurations of `w` is exactly `(5Q_M + 1)/m*(w)`.

*Proof.* (≥) If `(u,τ) ∈ P(w)` with `τ > 0` then `(u,0) ∈ P(w)`, since every constraint reads `a·u + τ ≤ b` and `τ ≥ 0`; hence
`u_{x_M} ≥ m*(w)`. (≤) Let `p₁ = (u¹,τ*(w))` and let `p₀ = (u⁰,0)` attain `m*(w)`. For `λ ∈ (0,1]` convexity gives
`p_λ = (1−λ)p₀ + λp₁ ∈ P(w)`, and its margin coordinate is `λ·τ*(w) > 0`, so `p_λ` is strictly realisable; its final reading is
`(1−λ)m*(w) + λu¹_{x_M} → m*(w)` as `λ → 0⁺`. ∎

Two consequences, and they are the reason the lemma is stated rather than assumed.

- **The ε → 0 escape is closed.** A word realisable only with a vanishing margin cannot smuggle in a larger `R` than the
  certificate reports: the certificate's value already *is* the limit along `ε → 0`, taken on the same polytope. The threshold
  being positive and the supremum being computed are one statement about `P(w)`, not two steps in sequence.
- **The bound is an upper bound, attained or not.** `R ≤ (5Q_M+1)/m*(w)` holds for every strictly realisable configuration
  whether or not the infimum is attained, which is all the cap argument uses.

## 4. Results: the ratio sweep  `[PROVED — exact finite certificate, per ratio bound]`

Exact rational arithmetic throughout. The two independent engines agree wherever both were run: `v3` (simplex) reproduces `v2`
(vertex enumeration) at `S = 5`, `S = 6` and `S = 8` — same value, same word, same margin each time — and both report no
realisable word at `S = 4`. Check the `S = 8` agreement first: both engines' outputs for it were stored from the original runs
(`order5_certificate_S8_v2.out`, `_S8_v3.out`). The `S = 4, 5, 6` outputs for both engines are now stored alongside them, after
an audit found this document citing a cross-check whose runs it had not kept.

| ratio bound `S` | lap bound `L` | sup `R` | extremal word | margin `τ` |
|---|---|---|---|---|
| 4 | 3 | — | no realisable word | — |
| 5–9 | 3–7 | **27/8 = 3.3750** | `(1,1), (2,1), (3,1)` | 1/5 |
| 10 | 7 | **31/9 = 3.4444** | `(1,2), (2,1), (1,3), (3,1), (2,2), (1,6)` | 24/821 |
| 11–18, 22, 26 | 8–20 | **31/9 = 3.4444** | same word, unchanged | 132/4165 |

> **Order 5, `S ≤ 26`.** Every arrangement of five runners whose subject has `d_max ≤ 26·d_min` satisfies `R ≤ 31/9 < 4`.
> Hence the cascade stops and **Existence holds for every such runner** (Corollary 6.4).

**`[CORRECTS v1]` The lap-1 ladder is extremal only up to `S = 9`.** v1 reported the optimum as the lap-1 ladder `(3/2)³ =
27/8` and recorded that the old lap-1 assumption was thereby *discharged* — promoted from assumption to corollary. The discharge
stands for `S ≤ 9` and is **false from `S = 10`**: the optimum there is a six-move word in which runner 1 sets **three**
times, at laps 2, 3 and 6, with settings by the others in between — so runner 1 returns twice. Returns are not a detail of the
extremal regime; at `S = 10` they *are* the extremal regime.

**`[CORRECTS v1]` The margin drops once, then holds.** At `S ≤ 9` the extremal word carries `τ = 1/5`; at `S = 10` it carries
`τ = 24/821 ≈ 0.029`; from `S = 11` through `S = 18` it is `132/4165 ≈ 0.0317` and does not move again. So the margin of the
extremal word is not being driven to zero by growing ratio. Stated exactly, because the table shows it: the margin changes
**twice** — at `S = 10` with the change of extremal word (`1/5 → 24/821`), and again at `S = 11` with **no** change of word and
in the **upward** direction (`24/821 ≈ 0.0292 → 132/4165 ≈ 0.0317`). What the table supports is the conclusion, not a
single-step mechanism.

**Consistency.** The exhaustive integer census (every 5-subset of `[1,26]`) never exceeded `R = 3.1429`; the resonant runs never
exceeded `1.4142`. Both sit below every entry in the table.

## 5. The sweep: `sup R(S)` is flat, not climbing  `[the worry raised and then refuted]`

The first two values moved the wrong way — `27/8 = 3.3750` then `31/9 = 3.4444`, numerator `+4`, denominator `+1`. The family
`(27+4j)/(8+j)` increases to `4` without reaching it, so that shape continued would keep every finite ratio under the cap while
denying any uniform margin — precisely the margin-collapse scenario §3 exists to guard against. It was recorded as the live risk
to the programme on the strength of two points.

**The sweep refutes it.** `sup R` is `31/9` at every ratio bound tested from 10 to 26 — eleven values, nine of them consecutive, the same
extremal word `(1,2), (2,1), (1,3), (3,1), (2,2), (1,6)` throughout, and the same margin `132/4165` from `S = 11` on. The value
steps once, at `S = 10`, and then does not move as the lap bound `L` grows from 7 to 20 and the word-length bound from 21 to 60
moves. Growing the search space stopped producing better words.

That is the shape the reduction wants: a supremum bounded away from the cap, uniformly over a widening ratio bound, rather than
one creeping toward it. It is not yet a proof of the unbounded case — the certificate is exhaustive only per ratio bound, and
nine values are nine values — but the extrapolation that would have sunk the programme is dead, and the burden now sits on
finding a word that beats `31/9` at some larger ratio rather than on explaining why the climb stops.

Why `31/9` is a plausible ceiling rather than an accident: `R = (5Q+1)/u`, so approaching 4 needs `5Q + 1 ≈ 4u` — a runner whose
reading is large *and* whose lap sits just under `(4u−1)/5`, the lap bound `L`. Large ratio makes the large reading available;
the sweep says the word conditions do **not** let the lap keep pace with it. The extremal stays at reading 9 and lap 6 no matter
how much more room the bound allows.

## 6. Cross-shift analysis of the resonant chains  `[EMPIRICAL — and one null was forced]`

The owner's question: do the long chains live inside one scale-cluster or traverse clusters? The answer decides whether
large-ratio reduces to bounded-ratio.

**v1 of the query answered "one cluster" and that answer was near-vacuous.** Its generator drew the three large speeds as a base
`b` times a multiplier in `[1,3]`, so the top cluster had ratio ≤ ~3 by construction: over 7200 walks with global ratio up to
2403, no window of five consecutive settings ever spanned a ratio above 3.14, and no cross-cluster handover was available to
observe. A statistic that could not have come out the other way is not evidence, and it is recorded as a defect of the query,
not a finding.

**v2 of the query puts the speeds at separated scales** (`two`: `{1, b, b·m}`; `three`: `{1, b, b·m, b·m²}`; `ladder`:
`1, m, m², m³`, all with `m ∈ [10,60]`), so a straddling window is genuinely available. Over 4800 walks per mode with ratio > 8:

| generator | median ratio | max moves | chains ≥ 10 moves | max window-5 setter ratio | cross-cluster handovers | max `R` |
|---|---|---|---|---|---|---|
| `v1` (clustered, the control) | 775 | 73 | 9 | 3.13 | 0 of 4800 | 1.2970 |
| `two` | 19 388 | 6 | 0 | 181.1 | 1255 of 4800 | 1.1004 |
| `three` | 369 903 | 4 | 0 | 3648.9 | 1713 of 4800 | 1.0829 |
| `ladder` | 39 304 | 3 | 0 | 3600.0 | 1050 of 4800 | 1.1110 |

Read plainly: **cross-cluster handovers do happen once the generator allows them, and the chains that contain them are short.**
Every chain reaching 10 or more moves came from the clustered control, and those show no handovers at all. Length and
cross-cluster traversal are anti-correlated in this sample.

**What this is worth.** It is consistent with the reduction — the chains that could accumulate `R` toward the cap are the ones
confined to a bounded-ratio family — and it is weak evidence for it, because random sampling never approaches the extremal
regime: the largest `R` anywhere in these 19 200 walks is `1.30`, against the exhaustive certificate's `3.44`. Random resonant
chains are simply not where the extremum lives, so their behaviour cannot carry the reduction. **The reduction is not a lemma
yet, and this query did not make it one.** The decisive instrument is the certificate at growing `S` (§5), which searches
exhaustively rather than sampling.

## 7. Status and what is next

- `[PROVED]` Existence at order 5 for `S ≤ 26`, by exact finite certificate; `R ≤ 31/9 < 4`. An inequality on purpose: §1's
  conditions are necessary only, so the enumeration bounds the true supremum from above rather than computing it.
- `[PROVED]` Margin realisability (§3): the threshold and the supremum are one statement about one polytope.
- `[OPEN]` Unbounded ratio. The sweep is done and flat (§5), which removes the climbing worry but does not close the case.
- `[OPEN]` The reduction of large ratio to bounded ratio. Not established; §6 explains why the sampling evidence is thin.
- `[PROVED — Lean]` The three finiteness bounds are formalised in `LonelyRunner/LRC/Cascade/Certificate.lean`: `cascadeR_zoneHi`
  (a setting of `x` at lap `Q` lands at `R = (n·Q+1)/u`), `nearest_setting_ge` / `nearest_never_sets` (the nearest runner's own
  settings land at `R ≥ n+1`, above any cap `≤ n+1`), `lap_lt_of_cascadeR_lt` and `lap_lt_of_ratio_le` (the lap is bounded by the
  reading, uniformly in the ratio), `laps_strictly_increase`, and `lap_mem_Icc` (every admissible lap lies in a fixed finite
  interval). Cascade gate: 170 theorems, axiom-clean, no `sorry`. **Still owed in Lean:** the word LP and the value `31/9`.
- **The pricing lemma stays warm.** Not to be formalised until the reduction question is answered; §4's correction is the
  reason, since returns turn out to sit in the extremal word rather than outside it.
- **The word count is the limit, and v1's reserved remedy is still the remedy.** Cost roughly doubles every two steps of `S`
  (52 s at `S = 14`, 198 s at `S = 18`), so the sweep cannot be pushed indefinitely by brute force. v1 reserved the **flank
  criterion** for exactly this case — it discards configurations from the sieve side — and that item is carried here unresolved,
  not dropped. Since extended: `S = 22` and `S = 26` both return `31/9` on the same word and the same margin, so the flat run now covers
  every ratio bound from 10 to 26.
