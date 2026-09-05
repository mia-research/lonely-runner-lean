# PREREG — Is the b=0 axis deficit the χ₂(y) 0.470 suppression, or broader?

**File:** `PREREG_y_channel_chi2_vs_axis_v1.md`  **Date:** 2026-07-21  **Status:** PRE-RUN. No multiplicative-character deficit spectrum computed.

**What this decides.** `RESULT_harmonic_deficit_locus_v1.md` located the sub-Rayleigh deficit on the b=0 (pure-y) axis. §3 there flags the open question: is this the recorded **χ₂(y) 0.470 half-saturation** (master M3/N1) re-expressed, or a distinct, broader y-channel suppression? This run answers it before any "new object" language is used. Model primes only; **no ECDLP/extraction/secp claim**.

---

## 1. OBJECT

`a₀=1`. `E:y²=x³+7`, prime order `n` (so `y_d≠0` for all `d=1..n-1`; no 2-torsion — F1).
- **Axis** `A(c) = U(1,0,c) = Σ_d e_n(d) e_p(c·y_d)`, `c=0..p-1`.
- **Multiplicative-y readouts** for every character `χ_k` of `F_p*` (`k=0..p-2`, `χ_k(g^j)=e_{p-1}(kj)`; `χ₂ = χ_{(p-1)/2}`):
  `V(k) = Σ_d χ_k(y_d) e_n(d)`.
- **Random target** `g_r(d)` iid unit phase: `A_r(c)`, `V_r(k)` identically.
- **Deficits:** `D_A(c)=|A(c)|−E_r|A_r(c)|`;  `D_V(k)=|V(k)|−E_r|V_r(k)|`.

---

## 2. FORCED FACTS — zero evidence

- **F1** `y_d≠0` ∀`d` (odd prime order ⇒ no 2-torsion). `χ_k(y_d)` always defined.
- **F2 Gauss identity `[VERIFY to machine precision]`:** `V(k) = (1/τ(χ̄_k))·Σ_{c=1}^{p-1} χ̄_k(c)·A(c)`. Establishes that each multiplicative-y readout — χ₂ included — is a linear functional of the axis `{A(c)}`. So the χ₂ readout is *one slice* of the axis by construction; this is the structural fact, not evidence of sameness.
- **F3** the aggregate axis deficit reproduces (`RESULT_...locus_v1` §1): input, not re-scored.

---

## 3. STATISTIC (frozen)

**The multiplicative-character deficit spectrum** `D_V(k)`, `k=1..p-2` (exclude trivial `k=0`).
Two pre-committed readouts of its shape:
- **χ₂ share** `S = |D_V(χ₂)| / Σ_k |D_V(k)|`, vs the uniform baseline `1/(p−2)`.
- **χ₂ rank** `ρ` = rank of `|D_V(χ₂)|` among all `|D_V(k)|` (1 = largest).
- **Residual axis deficit after removing χ₂:** reconstruct the axis with the χ₂ component zeroed (`A(c) − (χ₂-projection)`), recompute its mean magnitude deficit `D_A^{−χ₂}`; report as a fraction of the full axis deficit `D_A`.

**Calibration (control C1):** `|V(χ₂)|/√p` reproduces the recorded χ₂(y) saturation (`≈0.47`, band 0.432–0.500 per M3). If it does not, the χ₂ object is mis-computed → no verdict.

**Null (C2):** for a random target, `D_V(k) ≈ 0` for all `k` (flat), and `D_A^{−χ₂}/D_A ≈ 1` (removing one of `p` modes changes little). Fires by being flat.

---

## 4. DETERMINATION CRITERION (pre-committed, replicated over 7 primes 163–2089)

- **"Same object (the 0.47 relocated)"** iff, at a majority of primes: χ₂ is the dominant suppressed character (`ρ ≤ 3`) **AND** `S` ≫ uniform **AND** removing χ₂ largely removes the axis deficit (`D_A^{−χ₂}/D_A ≤ 0.5`).
- **"Distinct, broader y-suppression"** iff the suppression is spread: `D_V(k)` broadly negative across many `k`, `S` near-uniform, and `D_A^{−χ₂}/D_A ≈ 1` (χ₂ carries little of it).
- **"Intermediate"**: report which characters carry the deficit and the χ₂ fraction, without forcing a binary.

No result if C1 (calibration) or C2 (flat null) fails.

---

## 5. TAUTOLOGY / FLOAT / SCOPE

- No selector reads `d` or `a₀`-derived targets circularly: `A(c)`, `V(k)` are character sums over the point set; the deficit subtracts a matched random-target ensemble per mode. Comparisons are relative magnitudes vs the random null.
- Curve/group arithmetic + `(c,k)` grids exact int; float only in the character sums / magnitudes. No float threshold decides the verdict (the criterion uses ranks/shares/ratios reported per prime, replicated).
- Model primes 163–2089, `a₀=1`. Nothing transfers to `2²⁵⁶`. Output = characterization of *which characters carry the y-channel deficit*; no security claim.

---

## 6. OUTCOME → ACTION

- Same object → the b=0 locus is the χ₂(y) 0.470 suppression relocated to additive-harmonic language; **do not** enshrine a new object; note the relocation and stop. Probe #2 (d-predictivity) then tests the *known* channel, not a new one.
- Distinct/broader → the axis carries y-channel suppression beyond χ₂; name it as a distinct [EMPIRICAL] object, then probe #2 is worth its own prereg.

## Files
- `y_channel_chi2_vs_axis_v1.py` / `.log`; `RESULT_y_channel_chi2_vs_axis_v1.md`; `_DEVIATIONS.md` if any.
