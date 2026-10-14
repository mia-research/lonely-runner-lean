# The (e, k) route: depth, and the correction to "k is unbounded"

**T. Palelei.** v1, 2026-09-18. Findings from one session. Nothing here is a proof, and no grade moves.

Scripts: `experiments/n8/k_vs_S_v1.py`, `ek_coverage_v1.py`, `first_vs_any_v1.py`,
`grand_return_period_v1.py`, `period_vs_instant_v1.py`, `incomm_adversarial_R_v1.py`, `R_vs_S_v1.py`,
`slot_collision_v2.py`, `ap_fit_rule_v1.py`, `owner_scale_check_v1.py`,
`order8_certificate_v1.py` / `_v2.py`.

---

## 1. The correction that unblocks the route  `[VERIFIED — adversarial, stated ranges]`

`Cascade/Flanks.lean` records: *"This does not prove Existence — the required `k` is unbounded
(`bounded_k_attack_v1` reaches `k = 369`)."* True, and **uninformative**. That experiment's own witness
has `S = d_max/d_min ≈ 14,125`. It asked *is `k` bounded?* It never asked *is `k` bounded given `S`?*

Adversarial hill-climb per band (`k_vs_S_v1.py`), maximising the smallest `k` that works at any flank:

| `S` cap | 8 | 10 | 15 | 20 | 30 | 50 | 100 | 300 | 1000 |
|---|---|---|---|---|---|---|---|---|---|
| max min-`k` | 6 | 6 | 6 | 6 | 7 | 10 | 14 | 37 | 146 |

Roughly linear in `S`. **At the framework's own working range — `S ≤ 26`, where the order-5
certificate lives — `k ≤ 7`.** Random sampling agrees: `k ≤ 6` settles 24,000 of 24,000 sampled
subjects across `S ≤ 40` (`ek_coverage_v1.py`).

**The `k = 369` witness is trivial for the construction.** All eight of its subjects resolve in at
most 3 cascade moves with `R ≤ 1.17`, four of them at zero moves. The cascade reaches that `k = 369`
opening **in one move**, computing `⌈d·t − 1/8⌉` arithmetically. So the figure measures how long a
*search* takes, and the ledger's Part 4 test names that a **false blocker**. Register item 26,
arriving by a new door.

**Hard-for-search and hard-for-cascade are anti-correlated**: search-hard is `S ≈ 14,125` with
`R ≈ 1`; cascade-hard is `S ≈ 7.4` with `R ≈ 12`.

## 2. First-ness is the cost, not the obligation  `[VERIFIED — exact]`

Author, 2026-09-18: Theorem 6.2(b) proves the cascade lands on the *earliest* instant, but Existence
needs only *an* instant. Measured on the same subjects:

| arrangement | subject | cascade moves (**first**) | min `k`, any flank (**any**) |
|---|---|---|---|
| `(1,31,75,97,128,160,176,225)` | 1 | 23 | **4** |
| `(27,70,107,137,159,188,344,393)` | 393 | 28 | **6** |
| `(1,1975,5265,6910,8737,9589,11845,15135)` | 1 | 22 | **2** |
| `R`-extremal | 1 | 26 | **5** |
| hard band, 20,000 subjects | — | mean 2.16, max 17 | mean 1.04, **max 4** |

§6A already says first-ness is *"a proved property of its output, not a requirement placed on
anything."* The statement was clean; **the instrument imported the burden** — a cascade-word
enumeration carries depth 28 where the obligation needs depth 6. Facet of
`feedback-n8-no-prereg-no-imports`: a limit of the machinery chosen, written as a property of
the problem.

## 3. The scale is read off the arrangement  `[DERIVED — arithmetic]`

The opening `(k + 1/8)/e` **is** the `r = 1` spine instant of scale `D = e/(8k+1)`. So the flank route
*is* the scale route, with the scale a disparity divided by `8k+1` — read off the speeds, not searched.
That meets register items 22–24, which refuse a loop over the gap because `D = p/(8t)` re-asks the
output as the input.

Worked, `(11, 21, 22, 23, 26, 34, 35, 40)`:

| subject | min `k` | flank `e` | `D = e/(8k+1)` | instant |
|---|---|---|---|---|
| 11 | 0 | 10 | 10 | 1/80 |
| 21, 22, 23 | 0 | 1 | 1 | 1/8 |
| 26 | 0 | 3 | 3 | 1/24 |
| 34 | 1 | 8 | 8/9 | 9/64 |
| 35 | 3 | 9 | 9/25 | 25/72 |
| 40 | 0 | 5 | 5 | 1/40 |

Subjects 21–23 get `D = 1`, `t = 1/8` — the grid instant. The other four get **different** scales,
which the firewall permits: no global clock. At `D = 1` exactly four subjects are lonely, and the four
that are not are **exactly the two colliding residue pairs** (11 ≡ 35 ≡ 3, 26 ≡ 34 ≡ 2 mod 8) —
`FRAME_FREE_RESTATEMENT` §2B, a runner sharing its residue is never lonely at any grid time.

## 4. What forces large `k`  `[EMPIRICAL — residue characterisation]`

A runner blocks opening `k` at flank `e` when `k·f + ρ/8` lies within `1/8` of an integer, `f` the
fractional part of `ρ = u_i/u_e`. Blocking many consecutive openings needs `f` small, i.e. `u_i` near
an integer multiple of `u_e` — **§6.6's near-sharer**. Every `k ≥ 3` residue member has 1–4
near-integer ratios *at every flank*. So large `k` requires simultaneous near-sharers at all seven
flanks: proximity to the hyperplanes `u_i = A·u_j`. Exact algebra, no density.

## 5. Commensurability is not a case split  `[VERIFIED / EMPIRICAL]`

- **Refinement ladder** `[VERIFIED — exact]`: `(27,70,…,393+e)`, `e → 1/7` by decimal truncation. The
  period `1/gcd` moves by a factor of 2,000; **`u = d_min·t` is exactly invariant at `9/8`** and the
  move count is exactly invariant at 24. The period varies with denominators, discontinuously; the
  readings vary continuously. **The period is not the controlling variable.**
- **Adversarial, exact in `Q(√2)`, rank-2 incommensurability verified** `[EMPIRICAL — 7 min, not
  converged]`: best incommensurable `R = 11.9116` at `S = 7.4717`, against the commensurable record
  `R ≈ 11.96` at `S ≈ 7.44`. **0.4% apart, same `S`.**
- Periodicity does give, for commensurable disparities, a **decision procedure**: the cascade stops
  within `Σ_j d_j/G + 1` moves or a phase repeats and it provably never stops. Decidability per
  arrangement — **not** a proof over the class.

## 6. Where `R` lives  `[EMPIRICAL — directed search]`

`max R` is attained at `S ≈ 7.0–7.6` whatever cap is allowed; Theorem 4.8 forces `R = 1` for `S ≤ 7`.
`R` decays away from the band: `S ≈ 50 → 6.5`, `S ≈ 811 → 1.48`. Five independent searches converged
on the same extremal readings `(1, 2.36, 3.24, 4.18, 5.24, 5.85, 7.48)` — which is the historical hard
case `(1,31,75,97,128,160,176,225)` to within a few thousandths. **The difficulty of order 8 is a thin
shell just outside `S = 7`, and it looks like one configuration.**

## 7. Withdrawn from this session

- The difference-set slot analysis. It reconstructed an arrangement by putting the subject at **0** —
  a stationary runner, §6A — and picked one of up to 128 sign patterns. Redone on arrangements
  (`slot_collision_v2.py`): mean `R` still falls monotonically with slot crowding, but the tail
  structure moved and is withdrawn.
- Three candidate scale rules — minimal fit, margin-max all-8, margin-max front-4 — **refuted**: all
  three fail on `(11,21,22,23,26,34,35,40)`, serving no scale for some subject at any `r ≤ 400`.

## 8. The obligation with no time and no iteration  `[PROVED — Lean]`

Formalised 2026-09-18 in **`LonelyRunner/LRC/Cascade/ScaleCandidates.lean`**, seven declarations,
zero `sorry`, all within `[propext, Classical.choice, Quot.sound]`.

**The identity that does the work.** A flank opening *is* the first spine instant of a scale read
off the arrangement:

    flankOpening n e k = (k + 1/n)/e = 1 / (n · (e/(n·k+1)))

so `candidateScale n e k = e/(n·k+1)` — a disparity divided by `n·k+1`. Nothing is chosen
(`flankOpening_eq_spine`).

| declaration | statement |
|---|---|
| `candidateScale` | `e/(n·k+1)`, the scale of the opening |
| `flankOpening_eq_spine` | the opening is that scale's first spine instant |
| `own_reading` | at its own candidate scale a disparity reads **exactly** `n·k+1` |
| `candidate_clear_own` | so it is **clear there by construction** — distance exactly 1 from the multiple `n·k`, the threshold case |
| **`lonely_iff_exists_candidate_scale`** | **the subject is lonely at some positive instant ⟺ some candidate scale is clear for every disparity.** No quantifier over time, no iteration |
| `inWay_at_scale_interval` | `d` is in the way at scale `D` ⟺ `D > d`, or `D ∈ (d/(n·M+1), d/(n·M−1))` for some `M ≥ 1` |

**What the last one buys.** The bad scales are an **explicit union of open intervals on a
half-line** — one dimension, not the six of reading space — and the candidate scales are exactly
their **left endpoints**. So a good scale is a *gap*, and a gap is **named** by its endpoint rather
than inferred from a measure. That is what keeps the reformulation on the native side of §6A.

**Verified against the cascade** `[VERIFIED — 32,000 of 32,000, exact]`
(`experiments/n8/scale_interval_v1.py`): the cascade's final scale is the **largest clear endpoint
`d/(8M+1)` at or below `d_min`**, every time. So the cascade is a sort and a scan, not an
iteration; the winning candidate has median rank 1, mean 2.41, max 25 in that sample. The 28 moves
were the sort happening one comparison at a time.

**Grid versus AP, which is where this came from.** Reduce by `g`; write `u_i = π(i) + n·q_i`. At
`t = p/(ng)` the `q` part contributes `q_i·p` **whole revolutions** and vanishes mod 1. So a grid is
an AP whose runners have lapped extra whole times, and global isolation fails exactly when two
runners share a residue — i.e. their disparity is a multiple of `n·g`, i.e. they slot-share. The
arrangement-level failure and the subject-level slot-sharer are one condition, and the cure in both
cases is a scale at which "whole cycles" becomes "whole cycles **plus one slot**" — which is what
`own_reading` says every candidate does.

**Refuted in passing** `[EMPIRICAL]`: the sharer's own flank at `k = b` (where `d = 8b·g`) settles
only 26–38% (`sharer_split_v1.py`). And "needs `k ≥ 1`" is **not** the same as "has a slot-sharer at
`g`" — 51.8% have one, 35.8% need `k ≥ 1`.

## 9. Open, and the next target

The residue of §4 is the obligation. Stated in the framework's objects:

> For every arrangement and every subject, some disparity `e` and some `k ≤ K(S)` gives a lonely
> opening — equivalently, the subject is lonely at the `r = 1` spine instant of scale `e/(8k+1)`.

`K(S)` is measured, not proved. **A proof of `K(S) ≤ 6` for `S ≤ 20` would be the first bounded form
of Existence at order 8.** Note what it must not become: verifying that a union of band-cells covers
the reading region is a complement-emptiness computation, which §6A refuses. The criteria must
**name** the `(e, k)`.
