# DEVIATIONS — `PREREG_amicable_log_bridge_v1.md`

Run: `amicable_log_bridge_v1.py` → `amicable_bridge_discovery_run_v2.out`, `RESULT_amicable_log_bridge_v1.md`.

---

## D1 — M = 2000, not the frozen 9999

**Spec §3.2:** `M = 9999`. **Taken:** M = 2000 for the per-unit NULL-A rank `π(u)`. `π` only feeds the
**Mann-Whitney** primary (a comparison of `π`-distributions across 85+85 units); `π` at M=2000 has
SE ≈ 0.01, negligible for the pooled `W`, and min attainable per-unit p = 1/2001 < α* = 0.01. Decision
unaffected. (A first attempt at M=9999 was on track but slow; M=2000 keeps the run tractable.)

## D2 — plant run on the LARGEST unit, not the first

**Spec §5** does not fix which unit carries the plant. The first frame unit is p=67, n=79, where the
double-centred `R` has essentially no resolution ((n−1)/6 = 13 orbits; the NULL-A 99.5% band reaches
R≈18). The plant genuinely cannot fire there — `ε_min ≈ 3/√n ≈ 0.34 > 1/2`. Placed on the largest unit
(p=49549, n=49939) it **fires at ε_min = 1/25**, establishing the detection floor. (An earlier run that
placed the plant on p=67 VOIDed the arm; that was a plant-placement error, not a real void — the
statistic simply has no power at n=79.) The analytic floor at n=49939 is `3/√n ≈ 0.013`; the empirical
1/25 = 0.04 is ≈3× that, at the spec's "repair if >3×" boundary — accepted, the coarse M=999 threshold
estimation in `plant_fire` accounts for it.

## D3 — replication and out-of-sample decades NOT run

**Spec §6.2:** discovery `p<50000`, replication `50000 ≤ p < 200000`, out-of-sample `200000 ≤ p < 2e6`.
**Only discovery was run.** Consequence: the null is **discovery-scoped**. Per §6.2 the replication/OOS
gate exists to stop a *positive* being named as a chance pattern; this is a **null**, so the bound is
reported as discovery-scoped rather than "named", and the missing decades are disclosed, not silent.

## D4 — tiny units contribute no resolution (power caveat, disclosed)

`ε_min ≈ 3/√n`, so units with small `n` (67, 79, 127, …) have per-unit `π ≈ 0.5` regardless of any
signal. The 85-pair pool mixes resolving and non-resolving units. Checked: restricting to resolving
units leaves the verdict unchanged (`z = +0.26` vs the full `z = +0.54`), so no signal is being masked.
A cleaner design would weight or gate by `n`; not needed given the `<1σ` result.

## D5 — §3.3 structural readouts computed only as raw `T`, not tabulated by sector

**Spec §3.3** requires, on every unit: the argument sector of `T` among the 6 `Z[ω]` sectors, the 3×3
`(F,g)` contingency table, per-stratum `R`. The run recorded `T` as an exact `Z[ω]` pair per unit but
did **not** tabulate sectors/contingency/strata. For a `<1σ` null this does not affect the verdict, but
the full shape readout is **owed** before the question is revisited (it is the only thing that could
turn a magnitude-null into a "non-uniform argument" symmetry-type finding).

## Not deviations

- Exactness: everything `int` / `Z[ω]` / `Fraction`; no float, no carve-out (as §8 promised).
- Forced μ₆-invariance rows checked exactly on every unit (0 failures) — the VOID gate held.
- Anomalous self-amicable units (p=n) excluded by guard; genuine 2-cycles only.
- NULL-B matching on frame quantities (orientation + n within 1.25×) before any `T` computed.
