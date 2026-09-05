# DEVIATIONS — PREREG_twist_orbit_spectrum_v2.md

*Logged as they occurred, not retrospectively. Each is a change from the frozen spec or a pre-run
clarification.*

## Pre-run clarifications (from `experiment-designer` SIGN-OFF, before any structural read)

- **CL1.** The spec's line 48 phrase "DFT of `ρ` on `ℤ/L`" is loose; the governing definition is the
  **full-group character sum** `V̂(χ)=Σ_{a∈(ℤ/n)^×}V(a)χ(a)` (line 51). The agent verified `T` is
  representative-independent under this definition (`717.116…` identical across natural / positive /
  random gauges). The run implements the full-group form (double FFT: `V=FFT_n(c)`, then
  `FFT_{n−1}(W)` at admissible `j≡3 mod 6`). No verdict impact.
- **CL2.** The iid-sign robustness variant (spec §2.4) is the tiebreaker only if a future prime lands
  `T` within ~5% of p95. No S prime did (min p-value 0.029 ≫ any tie region), so it was not invoked.

## Execution deviations

- **D1 — PLANT-POS construction corrected during test-fires (instrument bug, not a spec change).**
  First implementation built the planted positive as a class-index tone `cos(2π·3·c/L)`, which maps to
  a **non-admissible** statistic-frequency (`j≡0 mod 6`), so the statistic could not see it — PLANT-POS
  failed to fire (0.5×). Fixed to the **admissible character's class-signature** `ρ[s]=exp(iπs/L)`
  (which `rebuild_W` maps exactly onto `χ_{j=3}`). PLANT-POS then fired at 4.1×/4.5×/6.3×, matching the
  gate's pre-run power analysis. The bug was in the *control*, not the primary; caught and fixed before
  the frozen gate run. Primary statistic and null unchanged.

- **D2 — C-JZERO implemented as the `μ₃`-energy-fraction test.** The spec (§4) says "run the full
  statistic on stratum J." The identical `μ₆`-class statistic is **ill-defined on `j≠0`** curves,
  because `V` there is odd but **not** `μ₃`-invariant (no CM by `ω`), so the forced-symmetry rebuild
  does not apply. The faithful, decidable substitute: the fraction of `V`'s multiplicative-spectral
  energy on `μ₃`-trivial characters — forced to `1` on `j=0` (our curve) and `≈⅓` on `j≠0`. This tests
  exactly what C-JZERO is for (is the controlled-for structure CM-specific), and confirmed it
  (`RESULT §3`). The full `j≠0` re-test of a *fired* character (spec's intent) is triggered only by a
  positive; the primary was null, so it was not required.

- **D3 — Secondary multiplicativity probe (`V(a)V(b)/V(ab)`, §6) deferred, not run.** It is a distinct
  3-index object; running it under-specified on the frozen window would risk a post-hoc statistic.
  Named as a next probe in `RESULT §4` for its own prereg instead.

- **D4 — ERRATUM (post-run): the in-sample reference set `I` was mixed-stratum.** §3 listed
  `I={13,43,127,163,211,349,397,433,547}`, but `13,349,397,433` are `p≡1 mod 12` (COS), where
  `χ₂(−1)=+1` makes `V` **even**, not odd — the odd-channel statistic is mis-specified there and those
  four reference rows are not interpretable. Valid SIN in-sample primes: `{43,127,163,211,547}`.
  **The out-of-sample stratum S is entirely `p≡7 mod 12` and is unaffected**; the primary verdict
  stands. Discovered during the forced-object sweep (`RESULT_twist_orbit_forced_landscape_v1.md §3`).

No deviation altered the primary statistic, the frozen sample, the null, or the pre-committed readings.
