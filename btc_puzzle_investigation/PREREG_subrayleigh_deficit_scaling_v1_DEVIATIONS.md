# DEVIATIONS — PREREG_subrayleigh_deficit_scaling_v1

Recorded from the p=151/211/349 smoke test (instrument check at the schedule's smallest primes,
per §4 E1 + §5 anchoring). These are calibration observations; the primary statistic (pooled slope
over 30 primes) and the §9 decision tree are unchanged.

## D1 — E1 target numeral corrected (prereg transcription slip; no effect)
Prereg §4 states `sum|U|^2 = 151^2 * 132 = 3,009,132`. The arithmetic is `22801 * 132 = 3,009,732`.
The implementation computes the target directly from the identity `p^2*(n-1)` and the check PASSES
(relerr 3.1e-16 at p=151). Only the prereg's printed numeral was wrong; the identity, the code, and
the check are correct.

## D2 — planted-control P3 is prime-dependent and unmet at small p (expected; not an instrument fault)
Prereg §4 P3 requires `|z| >= 3 for delta=1e-3 at EVERY prime`, predicting `|z|~4 at p=151`. Measured
`mu/sigmaM ~ 743` at p=151 (the prereg assumed ~4000), so a delta=1e-3 planted deficit yields implied
`|z| ~ 0.74`, not >=3. **This is not an instrument failure:** the REAL deficit's own per-prime
significance is `z ~ -1.1 (p=151), -0.4 (p=211), -2.2 (p=349)` — the effect itself is sub-3σ at small p
and grows with p (prior: -13.9σ at p=2089). A fixed-delta planted control at small p therefore probes
BELOW the effect's own power there.
- **What is retained (the instrument's real job):** P1/P2 — accuracy and monotonicity. M = mean|U| is
  exactly linear in |U|, so `V_delta=(1-delta)U0` yields `D_hat=delta` exactly; recovery is exact and
  monotone at every prime. The instrument can size a deficit; it just cannot reach |z|>=3 at small p
  for a deficit smaller than the effect itself.
- **Revised planted-control pass condition (deviation):** P1 (exact recovery) + P2 (monotone) at every
  prime; P3 (|z|>=3) evaluated only where the effect's own |z|>=3 (the larger primes). This does not
  touch the §9 verdict, which rests on the pooled slope + replication gate, not on P3.

## D3 — smoke test observed D at 3 of the 30 primes (disclosed)
E1/direction were checked at p=151,211,349 before the full run. The §9 decision rule is frozen and
independent of these three D values; no analysis choice was tuned to them. Observed (for the record):
D = +1.49e-3, +3.73e-4, +1.39e-3 — direction consistent (all sub-Rayleigh), and already showing the
large prime-to-prime scatter the prior run reported (⇒ level-2 const-vs-1/logp may ABSTAIN per §9;
level-1 persistent-vs-fades has far more margin).

## Compute deviation (if it occurs) — dtype/schedule fallback
If p=10357/12043 exhaust memory in complex128 fft2, they are run last and, if still infeasible, the
verdict is issued on the first 28 primes (Δln p 4.07, Sxx ~48 — ~95% of the leverage), recorded here
with the exact prime set used. complex64 is NOT used in the accumulation (float32 round-off ~1e-3 at
p~1e4 is comparable to the deficit); complex128 only.
