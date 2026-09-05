# "Outside the symmetry" v3 — CORRECTS the "flat/geometric" characterization

Date: 2026-07-18. Supersedes v2. Script `scratchpad/diag_mechanism.py`. **v2 error corrected:** v2 called
eps and the symmetrized norm N̄ "flat / geometric even on the quotient," and an earlier note called the
departure "not a leak / less predictable." All three claims were premature — they came from testing ONLY
the multiplicative (discrete-log) arrangement. Measuring the additive arrangement flips the picture.

## The localization (what was missed)
Statistic z-scores (peak R, spread N_eff) vs permutation null, p=100003:

| object | arrangement | z(peak R) | z(spread N_eff) | reading |
|---|---|---|---|---|
| eps | multiplicative (g^r, fold L) | −2.2 | +12.3 | flatter than random (hyperuniform shadow) |
| eps | **additive (x=1..p−1)** | **+4228** | **−226** | **MASSIVELY concentrated** |
| N̄ | multiplicative (g^r, fold L) | −3.9 | +31.6 | hyperuniform (low-freq suppressed) |
| N̄ | **additive (x=1..p−1)** | **+9668** | **−222** | **MASSIVELY concentrated** |

- eps/N̄ are enormously spectrally CONCENTRATED in the additive variable x (z≈+4000–9600). This dominant
  structure was never measured; the v1/v2 "flat/geometric" label came from the multiplicative test alone.
- Multiplicative autocorrelation (N̄): lag-1 = −0.107 (random ±0.008 → ~14σ negative), decaying by lag 4.
  Low-freq power bands [1,5)/[5,20)/[20,100) suppressed to ratio 0.39/0.74/0.70 of flat → hyperuniform.
- **Mechanism (partially identified):** eis(x) ≈ x reduced mod the lattice is piecewise-continuous, so
  eps/N̄ are additively SMOOTH → additive low-frequency concentration. The discrete-log map g^r scrambles
  that additive smoothness into a hyperuniform multiplicative sequence (the +12σ/+32σ, lag-1 anti-corr).

## Corrections to the record (epistemic)
- "flat / geometric even on the quotient" (v2): INCOMPLETE — true only in the multiplicative/character
  basis; the object is hugely concentrated additively. The v2 descended-character null still stands as
  what it measured (no MULTIPLICATIVE-character concentration), but it is not the whole object.
- "not a leak" / "less predictable": RETRACTED. Prejudged exploitability without knowing the mechanism;
  and "less predictable" is likely backwards (hyperuniformity = hidden long-range ORDER, not disorder).

## What is and is not now known
- KNOWN: eps/N̄ carry strong additive spectral concentration (smoothness in x) AND a hyperuniform
  multiplicative shadow (calibrated: +12σ eps, +32σ N̄; controls at median). This is real structure.
- HYPOTHESIS (to check, not a verdict): the additive concentration is the trivial continuity of the lift
  (about the FIELD element x, not the scalar d), hence probably not a d-handle. NOT yet established.
- UNKNOWN: whether either the additive smoothness or the hyperuniform shadow bears on the curve or d.
  Not prejudged. The lesson: characterize an object in BOTH the additive and multiplicative bases before
  calling it flat/geometric/not-a-leak — a single-basis null is not the object.
