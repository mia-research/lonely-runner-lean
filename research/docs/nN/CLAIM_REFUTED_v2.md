# Retraction: §7.3's claim is NOT refuted

2026-09-13, v2. **This supersedes `CLAIM_REFUTED_v1.md`, whose headline claim is withdrawn.**
Owner's correction.

---

## 1. The retraction

`CLAIM_REFUTED_v1.md` reported the speed set `(1, 1975, 5265, 6910, 8737, 9589, 11845,
15135)` as a counterexample to §7.3. **It is not a counterexample.** It is an edge case that
requires the AP gap to be chosen by the cascade rather than set to `d_min`.

The arithmetic in v1 is correct and stands. What was wrong was the framing: I took §7.1's
phrase *"form `d_min` from the two speed-neighbours"* as the whole procedure, fixed the AP
gap at `d_min = 1974`, and reported the resulting failure as a refutation. The framework
selects the AP gap through the lattice cascade; `d_min` is one candidate gap, not the
definition of the search.

`CASCADE_SHARPENED_v1.md` §2 already located the right band — `D ∈ [1241, 1451]` — and
already called the owner's `~1200` "the right object and the right magnitude". I wrote that
and then reported a refutation anyway. The conclusion did not follow from my own §2.

---

## 2. What is true instead

**The isolation instant exists and the framework finds it.** For the runner at speed `1`:

| | |
|---|---|
| `t = 7/11608` is a genuine isolation instant | **verified** — every phase at circle distance `≥ 1/8` |
| AP gaps `g` placing it inside the window `[1/(8g), 7/(8g)]` | `g ∈ [208, 1451]` |
| owner's estimate `~1200` | **inside the band** |
| at `g = 1451` | `u = 7/8` **exactly** — the AP's own isolation instant |

**And `~1200` works for the whole arrangement, not just the failing runner.** At `g = 1200`,
window `u ∈ [1/8, 7/8]`, exact BSM decision:

| runner | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|---|
| speed | 1 | 1975 | 5265 | 6910 | 8737 | 9589 | 11845 | 15135 |
| clear instants | 3 | 7 | 6 | 7 | 4 | 6 | 7 | 6 |

**Zero runners without a clear instant.**

The AP instants `t = p/(8g)` themselves clear for runners 2, 3 and 6 only; the other five are
found elsewhere in the window. That is the split the owner described — the AP instants carry
some runners and the finer search carries the rest.

## 3. The band, and where `d_min` sits

Sweeping every AP gap for this arrangement:

> **Every `g` from `1` to `1451` gives all eight runners a clear instant** — one contiguous
> band, no holes. Nothing in `[1452, 2600]` does.

`d_min = 1974` is **above** the band. That is the whole of the failure: the gap was set past
the point where the arrangement's lattices still clear. `1451` is exactly the `D_max` of
`CASCADE_SHARPENED_v1.md`, and `ρ_max = 1451/1974 = 0.735 < 1` is the flag that `d_min`
overshoots.

## 4. What else this retracts

`CLAIM_REFUTED_v1.md` §4 reported failures at `n = 6` and `n = 7` as evidence that the
refutation was not an `n = 8` accident. **Those are withdrawn too.** The search in
`failure_hunt_v1.py` normalises readings against `d_min` by construction, so the AP gap is
pinned at `d_min` throughout. Every hit it produces is a `d_min`-overshoot of the same kind,
not a framework failure. The script is still useful — it generates edge cases that exercise
the cascade — but not for the purpose v1 put it to.

## 5. What stands from v1

The exact arithmetic: the window at `g = d_min = 1974` does contain no clear instant for
that runner, verified four ways. That fact is what makes the arrangement a useful test of
the cascade. Also the recorded bug in v1 §3, and the observation that the runner is lonely
at `t = 67/110544` in lap 2 **of the `d_min` frame** — which in the `g = 1451` frame is not
lap 2 at all but `u = 7/8`, inside the first window.

## 6. What this was an error of

Not arithmetic — framing. The manuscript's §7.1 is a one-sentence summary of the procedure,
and I read it as the specification. The cascade is documented in
`experiments/n8/cascade_by_dmin_v1.py` and in `CASCADE_SHARPENED_v1.md`, which I had written
the same day. The check that would have caught it — *does the cascade find this runner?* —
was already run and answered **yes, 419 clearing lattices**, in `CASCADE_SHARPENED_v1.md`
§1. I reported a refutation over the top of my own evidence against it.

**LRC(8) was never in question, and §7.3's claim is open, not refuted.**
