# DEVIATIONS — PREREG_twist_orbit_monodromy_v1.md

## D1 — Independent sign-off did NOT complete (infrastructure, not merits)
The `experiment-designer` agent terminated on an API session cap (resets 20:00 Australia/Brisbane)
before emitting a SIGN-OFF/HOLD verdict. Its partial output flagged **one** concern: whether the
iid-SU(2) null (centered at the asymptotic `1/8`) is correctly matched to finite-p data, given all 7
in-sample `E[u⁴]` sat below `1/8`. Per the user's direction to continue, and because a re-spawn would
likely hit the same cap, the concern was **resolved object-level** (D2) rather than deferred. The other
sign-off criteria were pre-validated by the test-fires (C-FORCED, C-CROSS, PLANT-UNIF separation,
C-NOFLOAT all pass). **Disclosed in `RESULT_twist_orbit_monodromy_v1.md §5`; a retroactive independent
sign-off is advisable after the session reset.** This is the discipline gap of the run.

## D2 — Convergence test added to resolve the flagged finite-p concern
The prereg (§5, outcome row 3) already pre-committed the discriminator: *"deviation does NOT shrink
with p"* ⇒ reduction; shrinks ⇒ finite-p. Made it concrete in the gate: (i) small-L vs large-L half
mean deviation, (ii) linear extrapolation of `dev` vs `1/√L` to `L→∞`. Not a new statistic — an
explicit readout of the pre-committed trend criterion. Result: deficit vanishes out-of-sample (6/6
split, intercept `+0.0018 ≈ 0`) ⇒ finite-p, full SU(2). No change to the primary `E[u⁴]` or its band.

## D3 — E[u⁶] deferred to a float diagnostic
Prereg §2 listed exact `E[u⁶]` via `Σ R(j₁)R(j₂)R(−j₁−j₂)` (O(n²)). Kept as an in-sample preview
diagnostic only (`monodromy_preview_v1.py`); the gate reports the exact `E[u⁴]` primary alone, which is
the pre-committed discriminator. `E[u⁶]` is confirmatory and not needed for the verdict.

No deviation altered the primary statistic, the frozen sample, the null model, or the pre-committed
readings.
