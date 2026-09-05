# DEVIATIONS — harmonic_deficit_locus (prereg → run)

Departures from `PREREG_harmonic_deficit_locus_v1.md`, recorded for audit. None change the gate verdict.

1. **Gate operationalized as a majority rule.** The prereg said "extreme (perm-p<0.01) on the
   discovery set AND replicates (perm-p<0.05) on the replication set" without fixing a per-prime
   quorum. Implemented as: extreme-on-discovery = perm-p<0.01 at **≥2 of 3** discovery primes;
   replicates = perm-p<0.05 at **≥3 of 4** replication primes. The surviving locus (b=0) meets the
   strict all-primes reading too (≤0.006 on all 7), so the rule choice does not affect the verdict.

2. **Plant (C2) injected on ALL primes, not discovery-only.** The prereg text said "discovery set
   only," but a discovery-only plant would (correctly) fail the replication gate and test the FILTER,
   not the detector. The filter direction is already covered by the natural χ₃@163 chance pattern
   (C3). So C2 injects on all primes to test that the gate can flag a genuine replicating locus — it
   did (P1 perm-p ≤ 0.005, LOCUS). This is a stricter positive control than the spec's.

3. **Extension primes.** `4099` did not resolve a prime-order curve in the search window
   `[4099, 4139]`; `8209` was not attempted (compute-bound: `p²≈67M`-cell FFT × R × K). Both were
   report-only / not gated in the prereg, so the gated decision (7 primes, 163–2089) is unaffected.

4. **Direction follow-up** (`_axis_direction_check_v1.py`, exploratory) used axis mask `b=0 & c≠0`
   (pure-y, excluding (0,0)) vs off-axis `b≠0`, at p=433/577/991 only. It characterizes the sign of
   the already-located locus; it is not a new gated test.

5. **Parameters:** `R=200` random targets, `K=1000` locus-permutations (prereg required `K≥1000`).
