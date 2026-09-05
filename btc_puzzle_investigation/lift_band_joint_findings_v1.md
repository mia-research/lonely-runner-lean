# Lift-residual × Band-residual — joint object built & tested (v1, 2026-07-17)

**Question (user).** Until proven impossible, is there a subtle / sub-noise leak from `(x,y)` toward
the band decomposition `n,k,D,derr` — an interference pattern between two objects not obviously
linked? The specific corner: **non-bounded-degree** cheap readouts (the Eisenstein lift `eis(x)→(u,v)`,
flap `ε`, norm `s`) are lattice reductions, NOT bounded-degree rational functions on `E`, so the Part V
closure (KS/Weil) does **not** cover them. Every lift *law* we proved is about the **marginal** of
`eis(x_d)` over `d`; the **joint** `(eis(x_d), band(d))` was unbuilt. This builds and tests it.

Scripts: `lift_band_joint_v1.py` (sparse-sample MI leak test), `lift_band_spectral_v1.py` (full-group
spectral profile). Signal path exact int (eis/enorm/sextant/derr); float only in the MI/FFT/z
statistic layer, ranked against matched permutation / shuffle nulls; toy values < 2⁴⁰ (no bit loss).
`check_no_float` clean on the signal-path functions (AST-verified: `features`, `targets`,
`band_residual` integer-only).

---

## Part 1 — direct joint leak test (sparse point-cloud)  `[EMPIRICAL null, controls fired]`

**Setup.** Constructed (MT-pipeline) keys, **fixed bits=256 stratum, N=21,000** (App-A bit-length
confound avoided by fixing bits). Features from **public** `(X,Y)`, exact: `sextant, flap ε,
σ=sign(u−v), sign_u, sign_v, sign(xy), s=N(eis X)` + a `CTRL_Xlow = X mod 8` generic baseline. Targets
(stored decomposition, exact): `derr=|n·off−k·A|, k mod 8, n mod 8, D mod {8,16}, |D|`. MI
bias-corrected against a matched shuffle null (R=200) → `I_c` (bits), `z = I_c/σ_null`.

**Instrument validated.** Planted-leak targets FIRE (f=0.30 → z=+1120, I_c=+0.25 bits; f=0.05 → z=+33,
I_c=+0.007). Random target FLAT (z=−0.8). Power-scaling a planted f=0.05 leak on the 21k grid ramps
monotonically `z: 0.6→2.6→8.9→19.5→40.3` with a flat `I_c≈+0.010` plateau (the √N-signal signature).

**Result.** Across the full 8×6 grid, **every cell |z| ≤ 2.3**, and no lift feature beats the
`CTRL_Xlow` baseline (|z|_max = 2.2). The one faint wobble (`s × D_mod16` z=−2.3) appears **equally on
the raw-X control** (`CTRL_Xlow × D_mod16` z=+2.2), and the top cell power-scales as **noise** (sign
flips across N, no plateau) — look-elsewhere, not signal. Against `derr, n, k` everything sits at the
floor; the planted control on the identical grid fires and power-ramps.

**CORRECTION (2026-07-17 re-audit).** An earlier version called the D-channel wobble a "D-construction
tautology, D built from the point coordinates," citing `KNOWN_FACTS v5.1`. **That mechanism is false**
and was a dismissal-by-decree. `D = residual(d,N,n,k) = d − base_of(d,N,n,k)` (`exact_core.py`) is a
function of `d` only — `(X,Y)` is never used to compute `D`. So `D` is a legitimate `d`-mediated target
exactly like `derr/n/k`. Re-tested properly (`(X·Y)mod64 × D mod64`, matched null + power-scaling): at
the **floor** at bits=256 (z=0.4, noise) **and across all bit-lengths 11–160** (100k_exact; 0/≈150
strata fire, max |z|=3.7 = look-elsewhere). The `KNOWN_FACTS` "stable non-null" does **not** reproduce
in exact arithmetic (likely float-era, already flagged provisional in CLAUDE.md). The verdict (D at
floor) holds — but as a tested magnitude null, not a tautology.

**Real-82 cross-check** (`derr` stored): pooled (1 key/bits → bit-length confound uncontrolled, n=82
bias-dominated), max |z|=2.1 in a 24-cell grid = look-elsewhere; no consistency with any constructed
cell. Underpowered, consistent with the null.

**Scope / power ceiling.** Feature set = 7 lift/geometry readouts (8-cell binned); targets = band
residual + D low bits (8-cell); N=21k fixed-bits-256; floor = generic pseudorandom-feature (X-lowbit).
Sensitivity ≈ a **2% leak strength** would show (ref: planted 5% → z=40 here; 2% → z≈16). A
**sub-2%** (deeper sub-noise) coupling is NOT excluded — this is a scoped null, not a closure.

---

## Part 2 — full-group spectral profile (toy curves)  `[VERIFIED structure + EMPIRICAL null]`

Full band `d ∈ [A,2A)`, `A=2^(b−1)`, enumerated on three prime-order curves
(`n = 2089, 8293, 33151`). Per-mode `|FFT|²` vs a shuffle floor (white-in-d).

**★ POSITIVE — the band DENOMINATOR is a low-frequency law.** `k_den = n(d)` (the Farey denominator)
carries **low-frequency mass growing with curve size: excess 5.4× → 12.2× → 28.0×** over the white
floor, with a **stable top mode |f| = 12/24/24**. Growth-with-size ⇒ real structure, not finite-size
wobble. (Expected: the CF denominator is piecewise-constant on Farey intervals = intrinsically
low-frequency.)

**★ CORRECTION to the a-priori guess.** The residual **magnitude `derr(d)` is NOT low-frequency** —
excess **0.1–0.2×**, mass pushed to HIGH frequency (top mode 154→442→782, grows with L). So the
"fat low-freq spectrum" belongs to the **denominator**, not the residual magnitude. Measured, not
assumed.

**Curve lift readouts are WHITE in d.** `eis_u, eis_v, s, ε, sextant, sign(xy)` all have low-freq
excess **~1.0×** (0.7–1.3×, converging to 1.0 as L grows; the 1.4× wobble at n=2089 washes out by
n=33151). The non-bounded-degree lift buys **no** non-whiteness in `d`.

**No interference / no shared mode.** Overlap of each curve-readout low-freq power spectrum with both
`derr` and `k_den`: **every |z| < 1.8** across all three curves. The loophole (a non-flat curve readout
overlapping the band's structured modes) is not realized — because the curve readouts are flat.

---

## What this does and does NOT establish

- **BUILT** the joint object the closure does not cover, via two lenses (sparse MI, full-group
  spectrum). `[done]`
- **Positive structure found:** `k_den` low-frequency law (new spectral characterization of the band
  decomposition), stable top mode |f|=24, growing excess. `[VERIFIED, toy p≤33k]`
- **Magnitude reading (scoped):** in the lift/geometry features tested, joint coupling to `derr/n/k` is
  below ~2% leak strength at the tested scale, and the toy lift readouts' low-frequency mass is at the
  white floor. `[EMPIRICAL, controls fired]`. This is a bound on those features at that floor — it does
  **NOT** establish that `eis(x_d)` is white-in-d in general, that the lift "cannot" couple, or that the
  closure's conclusion "extends" to non-bounded-degree readouts. No analytical/closure claim is made.
- **NOT done — the genuine open frontier (matches the user's "unless analytically proven otherwise"):**
  1. **Lift-white-in-d is empirical.** An analytical statement — "`eis(x_d)` has no low-frequency mode
     in `d`" — would be the closure-extension to non-bounded-degree lattice readouts. Unproven.
  2. **The amicable-slippage mechanism is unprobed.** Toy curves cannot test it: the secp-specific
     `π_n = π_p − 1` near-coincidence of the two CM rhombi (slippage `(0,1),(1,1)`) is exactly the
     "not obviously linked" channel; a scalar-side lift `eis_n(d)` vs field-side `eis_p(x_d)` structural
     probe on the real keys is the next object. (v12 left `(π_p−1)(π_n−1)` open.)
  3. **D-signature terms** (`d2..d6` on `100k_exact`) untested spectrally; **sub-2%** leak strength not
     excluded; finer band resolution / other bit-strata unswept.

*Grade legend: PROVED · VERIFIED (exact/numeric at scale) · EMPIRICAL (scoped, controls fired) · CITED.*
