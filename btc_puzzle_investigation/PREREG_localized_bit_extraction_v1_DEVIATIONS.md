# DEVIATIONS from PREREG_localized_bit_extraction_v1.md

All deviations below were decided **before** the replication data were computed, and each is forced
by an algebraic identity or a measured pipeline defect — none by a result. Logged per the project's
prereg discipline.

---

## D1. §5 two-generator replication arm is NOT independent — it is the matched null. **FIXED.**

**The prereg says** (§5): "four further primes ... and **two distinct generators each** (`G` and
`[s]G` for a fixed `s = 7`), giving **8 independent replication runs**", and requires a cell to fire
in `>= 7 of 8` to be named.

**The identity.** With `G' = [7]G`, the point at scalar `d` is
`P'_d = [d]G' = [d][7]G = [7d]G = P_{7d}`.
So the generator-`[7]G` run pairs `F(P_{7d})` with `T(d)`. That is **exactly null 2a with `t = 7`**
(§2a: "pair `F(P_{t*d mod n})` with `T(d)`").

Verified as an exact identity, not an approximation:
`P_d^{[7]G} == P_{7d}^{G}` for all `d = 1..n-1` at `p = 127`. (`lbe_harness_v1`, generator check.)

**Why this inverts the verdict.** Null 2a is *designed* to destroy the feature-scalar pairing. A
genuine leak is therefore expected to fire on `G` and **not** on `[7]G`. Under the `>= 7/8` rule as
written, a real signal fails replication and is discarded as a chance pattern (outcome H2), while
the only cells that could pass are those invariant under `d -> t*d` — which §2a already pre-states
are **invisible** to the matched null and are feature-marginal statements, not leakage (outcome S2).
As written, §5 selects against the hypothesis under test.

**Amendment (pre-data).**
1. **Replication is across PRIMES only**, using the canonical generator returned by
   `prime_order_curve` for each prime. The replication criterion becomes `>= 4 of 5` primes
   (uncorrected `P < 0.01`), with §5 criteria (2) residual-structure consistency and (3) effect size
   `>= e_min/2` unchanged.
2. **The generator arm is re-purposed as a control row, not a replicate.** For any cell that fires,
   the `[7]G` run is computed and *must behave like the null*. If a cell fires equally under `[7]G`,
   it is invariant under the relabel and is reported as **outcome S2 (feature-marginal law), not
   leakage**.

**Scope of the change.** This weakens the replication requirement from 7/8 to 4/5 runs. It does not
touch the statistic, the null, the plant ladder, the family-wise rule, or any outcome cell.

---

## D2. Cap-Law feature required a per-prime basis-orientation constant. **FIXED, disclosed.**

**Measured.** The prereg's feature `A5` ("normalized cap distance `|u-v|` binned at the 1/2
threshold") does not track `eps != 0` under the naive reading. Across 12 primes the agreement is
**bimodal**: exactly `1.000` on some primes and `~0.49` on the rest, with the two flap sets
*disjoint* on the latter (agreement = 1 - both rates) and both carrying the correct `~1/4` density.

**Cause.** The reduced basis is defined up to an orientation that exchanges which of `|u-v|`,
`|u+v|` is the Cap-Law invariant. For **every** prime tested, exactly one of the two agrees on all
`p-1` points and the other is disjoint from it.

**Amendment.** `cap(X)` fixes the orientation by majority vote over the same `>=1000` probes used
for `beta`, requiring `>=99%` agreement (else the prime aborts, as for `beta`, outcome P3).

**Honesty note on what this verifies.** After calibration the Cap Law holds `126/126` at `p=127`.
The calibration consumes **1 bit** per prime; the unforced content is therefore `(p-1) - 1` bits of
agreement, not `p-1`. Stated that way per the "count only unforced hits" rule. The calibration reads
only the feature side (`eps` vs `cap`) and never sees a target, so disjoint construction (§0) holds.

**Consequence for the grid.** After this fix `A3_flap` and `A5_cap_half` are the *same partition*
(that coincidence IS the Cap Law). They are retained as separate cells so the frozen grid and `K`
are unchanged; the duplication is disclosed and only makes Holm slightly more conservative.

---

## D3. chi2 calibration fails at small `n`; Bartlett-type correction added. **DISCLOSED.**

At `p = 127` (`N = 126`), `173/210` cells fail the §2c KS check against `chi2_df`. The prereg
prescribes falling back to the empirical matched-null quantile, but 200 (or even 2000) draws cannot
resolve a p-value at the family-wise threshold `alpha/K ~ 5e-5`.

**Amendment.** Primary p-values use a Bartlett-type rescaling `G' = G * df / mean(G_null_2a)`,
estimated from the §2c null draws, compared to `chi2_df`. The raw `P`, the corrected `P_corr`, and
the exact integer empirical rank `emp_p` are all reported per cell. No verdict rests on a cell whose
three readings disagree in direction; such a cell routes to replication.

**Consequence.** Small primes (`N < 5000`) are power-starved regardless (measured `e_min = 0.5` at
`p=127`), and the prereg already bars them from the scaling arm. They contribute to replication
counting only.
