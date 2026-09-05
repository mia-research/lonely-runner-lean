# The y-channel (parity-correct readout) into the scalar lift eis_n(d) — v1, 2026-07-17

**Premise.** The parity result (`slippage_algebra_findings_v1.md`) proved `eis_p(X_d)` is EVEN in `d`,
`eis_n(d)` is ODD in `d`, so the `x`-lift alone cannot reach `eis_n(d)` linearly. `y_d` is ODD in `d`,
so a `y`-using readout is parity-correct; and `sign(xy)` (`x` even × `y` odd ⇒ odd, μ₃-weight-1) sits in
the **same isotypic sector** as `eis_n(d)`. Question: does the symmetry-matched cheap readout actually
correlate with the scalar lift above the √n floor, or does reaching it still need the DLP?
Script: `y_channel_eisn_v1.py`. Exact-int signal path; float only in MI/z vs matched shuffle null.

## (A) Sector alignment  `[VERIFIED]`
`eis_n(λd)` is a unit-rotation of `eis_n(d)` (10/10; μ₃/μ₆-covariant, `λ³≡1 mod n`). `xy(βx,y)=β·xy`
(μ₃-weight-1) and `xy` is odd in `d`. So `sign(xy)` and `eis_n(d)` genuinely share the odd+μ₃-weight-1
sector — the parity+μ₃-correct readout. Occupying the right sector is **necessary, not sufficient**.

## Instrument note (control caught a bug)
First Part-B run gave MI ≡ 0 including the aligned ceiling (z=0.0) — a dead instrument. Cause: toy
readouts encoded `±1`, but `mi_bits` indexes a contingency table by label and `−1` wraps to the last
row, collapsing the feature. Fixed to `{0,1}`; ceiling then fires and **grows** with n (z=104→417→1442),
so the detector is valid. (The "check the control row fires before believing any verdict" rule earned
its keep.)

## (B) Toy full-group: does the cheap odd readout reach eis_n(d)?  `[EMPIRICAL — floor-bounded, non-scaling]`
Full-group MI of `sign(xy)`, `s_y` vs `eis_n` targets (`sextant_n`, `sign u_n`), shuffle-null z, across
prime-order curves with `n ≡ 1 mod 3`.
- `sign(xy)` is at the floor on every curve (|z| ≤ 1.4).
- `s_y × sextant_n` scanned over **18 curves** (n = 1093 … 45523): **4/18 exceed |z|=2** (z=8.2 at
  n=2143; 3.3, 3.6, 2.2 elsewhere), the rest at the floor. Crucially the spikes **do not scale** — the
  largest are at n=2143 *and* n=36697, no monotone growth, signs mixed. A real coupling grows with n
  (the ceiling grows 104→1442); this does not.
- **Reading:** the parity+μ₃-correct readout does **not** reach `eis_n(d)` with a scaling signal; the
  correlation is floor-bounded asymptotically. Occupying the sector opens the door; the magnitude inside
  it stays at the floor.
- **Flagged open, NOT dismissed:** 4/18 curves above |z|=2 is more than the ~1 expected by chance, so a
  *minority of individual small curves* carry genuine weak `s_y↔sextant_n` correlation. It is
  non-scaling and secp-absent (below), and I do not have an explanation (candidate: special `π_n` forms
  on those curves). Open micro-observation, not a leak.

## (C) secp 36k bits=256 (21k) substrate  `[EMPIRICAL — at floor]`
Cheap odd PUBLIC readouts {`sign_xy`, `s_y`, `y_low3`} → `eis_n(d)` targets {`sextant_n`, `sign u_n`,
`u_n_bin`}. Instrument valid (planted z=1049/29; random flat). Whole grid |z| ≤ 2.1; top cell
`s_y × u_n_bin` (z=2.1) does not beat the raw-`X` baseline (1.5) and does **not** power-ramp
(z: 0.09,−0.43,0.08,0.38,0.96,1.65 — noise). No y-readout reaches `eis_n(d)` above the floor here.

## What this establishes / leaves open  (read literally)
- **Establishes (VERIFIED):** `sign(xy)`/`s_y` and `eis_n(d)` share the odd+μ₃ sector — the parity
  obstruction is genuinely bypassed at the symmetry level.
- **Establishes (magnitude, scoped):** in these specific cheap odd readouts vs `eis_n`'s sextant/sign,
  the correlation is floor-bounded — non-scaling on toy full groups, at the raw-`X` floor on 21k secp
  keys, controls firing. A bound on those readouts at those floors. Not independence, not a closure.
- **Open:** richer/μ₃-phase-exact `y`-readouts; sub-floor strength; the unexplained per-curve toy
  excess; and any **analytical** statement — e.g. whether the closure's √p bound extends from the
  character `e_n(a·d)` to the non-bounded-degree target `eis_n(d)` via its Fourier/Wiener profile (the
  same loophole as the band case). Reaching the *full* odd content of `eis_n(d)` still resolves `d` = the
  DLP; whether a *fraction* leaks cheaply is not settled by these readouts.

*Grades: VERIFIED (sector alignment; control-validated instrument) · EMPIRICAL (floor-bounded, controls
fired) · OPEN (richer readouts, per-curve excess, analytical bound). No closure claimed.*
