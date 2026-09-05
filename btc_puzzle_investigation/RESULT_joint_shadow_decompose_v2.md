# Joint (x,y) shadow — v2: char-vs-random control on the v16 "0.93"

Date: 2026-07-18. Script `joint_shadow_decompose_v1.py`. Model curves `E: y²=x³+7`,
prime order, p ∈ {163, 349, 433, 577}. a₀=1. **Supersedes v1**, which asserted an
unverified mechanism ("joint rho2≈1 because |U| is flat") and used dismissal language
for the 50/50 split. Both are corrected here **by measurement**, not by re-wording.

## Reproduces (unchanged)
- v16's `rho_inf = |Corr|/‖F‖_∞`: **joint 0.93–0.96, x-only 0.29–0.36**, stable across 4 primes.
  (v16's code `/√n` printout and its coefficient-count `norm_inf` are neither the metric; `rho_inf`
  under the true point-space sup-norm is.)
- The **exact even/odd constraint** `U(−a,b,c)=U(a,b,−c)`: x-only readouts are even-in-d (x_d↔±d),
  so they see only the even half of the d-spectrum; the odd half needs y (y_{−d}=−y_d). C3 cross-
  orthogonality `⟨F_even,c_odd⟩=⟨F_odd,c_even⟩` = 1e-15 exact. This is a real structural fact:
  which *half* of d each coordinate can carry.

## The decisive control — char vs RANDOM target (phase-only reconstruction fidelity)
Same phase-only aligned readout, applied to the leaking character `e_n(a₀d)` and to a random
unit-phase function of d, on each support:

| p | joint char | joint random | x-only char | x-only random |
|---|---|---|---|---|
| 163 | 0.9992 | 0.9993 | 0.6699 | 0.6881 |
| 349 | 0.9996 | 0.9997 | 0.6734 | 0.6749 |
| 433 | 0.9997 | 0.9997 | 0.6633 | 0.6723 |
| 577 | 0.9997 | 0.9997 | 0.6588 | 0.6609 |

**The reconstruction magnitudes do not distinguish the character from a random function of d.**
Hence the numbers 0.999 (joint) and 0.66 (x-only) — and therefore v16's `rho_inf` 0.93 / 0.34 —
measure the phase-only reconstruction quality of the (x,y) coordinate geometry, not a d-specific
property. The joint > x-only gap is real but present for any target (two coordinates reconstruct
better than one). Joint ≈ 1 is the bijection P↔d: the point determines the scalar, so any
function of d is reconstructible from (x,y).

## Forced / generic / structural — verified, not asserted
- **joint rho2≈1**: char = random (Δ<0.001) → not d-specific; = the P↔d bijection.
- **50/50 even/odd split**: forced by (generic rho2≈1) + (character energy is ½ even, ½ odd).
  v1 attributed this to a "flat |U|" mechanism — **that was wrong: |U| flatness = 0.78** (mean|U|
  ≈ 0.88·RMS, RMS ≈ √n per Parseval, max ≈ 3.0–3.4 √p). The correct backing is the char-vs-random
  control above.
- **x-only ceiling 1/√2 = 0.707**: exact (even-subspace bound); the measured 0.66 is generic
  phase-recon of that subspace (char ≈ random).

## Untested — what the scalar control cannot see (do NOT conclude "all generic")
The char-vs-random control compares only the scalar fidelity. It does **not** test whether the
*frequency-support pattern* — which (b,c) carry the alignment, and their μ3/GLV-weight grading —
differs between the character and a random target. A generic magnitude is consistent with a
character-specific pattern. That is the open object, unmeasured here.

## Flagged sub-observation (not banked)
x-only char runs **consistently ~0.01–0.02 below** x-only random at all four primes
(0.6699<0.6881, 0.6734<0.6749, 0.6633<0.6723, 0.6588<0.6609). Direction-consistent but tiny, and
tested against a **single** random seed. Whether real (the character's even part is marginally
harder for an x-only phase-recon than a generic even target) or seed noise is untested — needs a
multi-seed null to place char in the random distribution.

## Scope
Enumerable model primes p ≤ 577, single CM family y²=x³+7 (j=0). secp (order ≈ 2²⁵⁶) not
enumerable. No exploitability assessed — object structure only.

## Correction log vs v1
1. v1: "joint rho2≈1 because |U| is flat" — refuted (flatness 0.78; the real reason is generic
   reconstruction, char=random).
2. v1: "50/50 split is forced … arithmetic, not a discovered symmetry" — the *forced* verdict is
   correct but was reached by assertion; now backed by the control. Dropped the dismissal framing.
3. v1 implicitly still treated 0.93 as a meaningful joint-leak magnitude. The char-vs-random
   control demotes the magnitude to generic (coordinate-geometry) reconstruction; the d-specific
   content that survives is the exact even/odd constraint and (untested) the frequency pattern.
