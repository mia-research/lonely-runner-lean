# Result — the 2-adic witness route at n=8 is closed, and the reason is density

2026-09-07. Audits the run specified by `docs/n8/PREREG_DYADIC_DEPTH_v1.md` against
that specification. Artifacts: `experiments/n8/{two_adic_witness_v1,
dyadic_depth_v1, dyadic_forced_v1}.py`, outputs in `experiments/n8/*.out`.

**`[PROVISIONAL — experiment-designer gate not run]`** — see the pre-registration's
header and §6 for what a self-audit here does and does not cover. No grade is
promoted on the strength of this run.

## 1. What was tested

`κ(T)` = least `k ≥ 3` admitting an odd `a` with `‖v·a/2^k‖ ≥ 1/8` for every `v ∈ T`;
**H1**: `κ` bounded by an absolute constant on the residual hard case `R` (sets
holding a multiple of 5, 6, 7 and 8). The motivation was that `n = 8 = 2^3` makes the
condition automatic whenever `k - v_2(v) ≤ 3`, which looked like arithmetic leverage
no other `n` has.

## 2. Outcome against the pre-committed table

**H1 fails as stated.** `max κ` grows with the speed bound, 20 000 sampled sets per `V`:

| `V` | 50 | 100 | 200 | 400 | 800 |
|---|---|---|---|---|---|
| `max κ` | 7 | 8 | 8 | 9 | 10 |
| unsettled at `k ≤ 16` | 0 | 0 | 0 | 0 | 0 |

The pre-committed row for this observation reads: *"H1 fails as stated. Record the
growth; the reduction survives only as a `V`-dependent statement."* `κ` rises by ~3
over a four-fold doubling of `V`, consistent with `κ ≈ log₂V + c`.

## 3. The control did not fire, and the main figure is void as specified

The pre-registration's control clause: *"If the control reports zero failures, the
harness is broken and the main result is void."* At threshold `1/7` the sampler
returned **0 unsettled** at both `V = 50` and `V = 200`. So the `0 unsettled` row of
§2 is **void as evidence**, by this file's own pre-registration.

**Diagnosis — the control was mis-specified, not the harness.** It drew from `R`,
where almost every set has `M(T) > 1/7`, so a dyadic `1/7`-witness was forced there
too. A corrected control on sets with `M(T) < 1/7` known exactly — the three tight
instances (`M = 1/8`) and two near-tight sets (`M = 2/15`) — returns `κ@(1/7) = None`
for all five while `κ@(1/8)` is finite for all five. **The harness fires.**

## 4. Why the zero was forced  `[PROVED]`

`g(t) = min_v ‖v t‖` is continuous. If `M(T) > 1/8` then `g > 1/8` on an open
interval, and the dyadics are dense, so a dyadic witness **exists for every such `T`**
with no input from the 2-adic structure whatever. LRC(8) gives `M(T) ≥ 1/8`, and the
only sets left are the tight ones, whose good set was computed to be
`{1/8,3/8,5/8,7/8}` — already dyadic. So no `T` could ever have come out unsettled.

The `0 unsettled` figure therefore measures the density of the dyadics, not any
property of `T`. `dyadic_forced_v1.py` confirms the mechanism directly: `κ` is
bounded above by `⌈log₂(1/w)⌉ + 1` where `w` is the widest good interval — the
resolution needed to land in a gap — in every row sampled.

**One thing survives, and it is small.** `κ` runs well *below* that bound (within 2 of
it in 8 of 30 rows, below it in all 30), so dyadics land in the good gaps more
efficiently than a generic point would. That is a statement about efficiency, not a
proof route, and nothing here is built on it.

## 5. Ledger

The 2-adic witness family gives no leverage on `n = 8`: existence is forced by
density plus LRC(8), and the depth is unbounded. The route is closed **for this
stated reason** — not by a null. What is *not* claimed: that 2-adic structure is
irrelevant to `n = 8` generally; only this witness family, at this threshold, is
settled. Cost: one pre-registered run, caught by its own control clause.
