# Addition-lift, two-domain residue, S₃ covariant law — findings (v2, 2026-07-14)

Supersedes v1 (folds in the de-tautologized two-domain decomposition and the S₃
covariant addition-coordinate test). Companion to `POSITIVE_FINDINGS_HANDOVER_2_v1.md`.
This session attacked the one operation the Eisenstein lift does **not** already
linearize — point **addition** (the DLP-bearing op) — across three framings. All
arithmetic exact in the point/lift/label path; float only in MI/z rank statistics
vs a matched permutation null. Every result is **EMPIRICAL, scoped** — bound to the
labels / sample size / bridge stated — **not closure**.

## Scripts
- `glv_addition_lift_conditioned_v1.py` — addition law in π_p frame, CM-conditioned.
- `glv_addition_eps_reprobe_v1.py` — large-N settle of the ε reading.
- `glv_two_domain_residue_v2.py` — corrected two-domain residue (boundedness + non-circ leakage).
- `glv_two_domain_residue_v3.py` — de-tautologized artifact decomposition (TRUE vs artifact baseline).
- `glv_s3_addition_covariant_v1.py` — the S₃ covariant y-free coordinate σ₁ label law.

## 1. Coordinate (π_p) frame — CM-conditioned addition
No cheap label is a homomorphism under P⊕Q:
- **sextant / norm-band:** clean `MI~1/N` noise (sextant z +2.4→+0.4 is the small-N echo).
- **naive additive correction** `U_S−U_P−U_Q`: fully spread inside every (ε_P,ε_Q),
  (s_P,s_Q) cell. (Wrong baseline — group law is `x_S=λ²−x_P−x_Q`; see §3.)
- **ε (μ₃-orbit):** at N=180k, MI plateaus ~0.0001 bit while null falls ~1/N, so
  z climbs to +2.42 (control −0.41). A **faint, expected** residual (x_S is a
  group-law function of x_P,x_Q, so their geometric labels can't be independent),
  ~0.0001 bit of ε_S's ~1.06-bit entropy — **ε is NOT a homomorphism**. ε marginal
  on curve points 0.7500:0.1285:0.1216 (single-point 3/4:1/8:1/8 confirmed).

## 2. Two-domain residue vs the amicable bridge
`w=eis_n(d)`, `v=eis_p(x([d]G))`, `Mw`=w's π_n-cell re-embedded in π_p basis;
slippage confirmed `(0,1),(1,1)`.
- **v1 tautology (retracted):** correlating `r=v−w` vs `w` gave `MI=0.48–0.64, z=+5000`
  — a subtraction artifact (r built from w); the shuffle-control passes and thereby
  *masks* it. Recorded as `feedback_residue_vs_component_tautology`.
- **v2 boundedness:** `r=v−Mw` fills P_p (distinct 90000/90000, N(r)~257 bits) ⇒
  coordinate map **not** linear-up-to-wrap. Non-circular leakage
  (sextant(v)/eps(v) vs scalar labels & d mod 6) all null at N=90k, controls clean.
- **v3 de-tautologization (the correct dissection of the artifact):** the bridge
  `M·w` is a **4-cell quantization** of the scalar lift — cells
  `{(0,−1),(0,0),(−1,0),(−1,−1)}`, ~20k each — which is *why* r_slip (0.64) beats
  r_raw (0.48). Decomposing TRUE vs an artifact baseline that keeps the subtraction
  geometry and breaks only the d↔x pairing: **EXCESS z ≈ 0, non-scaling** (raw
  −1.32/+0.25/−1.32; slip −0.14/−0.36/−1.92, i.e. slightly negative). The
  tautology is pure subtraction geometry over a 4-cell bridge, with **no d↔x
  coupling riding on it** — established by the correct control, not asserted.

## 3. S₃ covariant addition coordinate (the correct nonlinear object)
The third summation polynomial is a quadratic in x_S; its roots are `x_{P+Q},
x_{P−Q}`, so the symmetric functions
   `σ₁ = x_{P+Q}+x_{P−Q} = −B/A`,  `σ₂ = x_{P+Q}·x_{P−Q} = C/A`
are **rational in (x_P,x_Q) alone — no y, no DLP** (the y-free part of the group law).
- **Validated 400/400:** σ == symmetric functions of the actual x(P±Q).
- **β-covariance 400/400:** `σ₁→β·σ₁` (weight-1, a coordinate), `σ₂→β²·σ₂`.
  ε(σ₁) marginal 0.7524:0.1236:0.1240 (single-point law holds on σ₁).
- **Label law — scoped null:** `(ε_P,ε_Q)→ε(σ₁)` z +0.5 with **control +0.52**
  (null-miscalibration, not signal); `(s_P,s_Q)→sextant(σ₁)` z +1.08→+0.23
  declining; `(ε_P,ε_Q)→ε(σ₂)` negative. On the *correct* covariant object, the
  CM labels of x_P,x_Q do **not** predict σ₁'s label beyond the floor.

## 4. What was established, and what these probes did (bias-audited)
**Positive structure established:** σ₁/σ₂ construction + [ω]-covariance verified on curve
points (400/400); the amicable bridge's exact 4-cell quantization of the scalar lift;
the ε 3/4:1/8:1/8 law on curve points. **Probes run:** whether the group law linearizes
/ leaks via the additive baseline (§1), the two-domain bridge (§2), and the CM-covariant
object σ₁ (§3) — each was **flat at the label resolution / N≤180k tested**, controls
clean. These are scoped EMPIRICAL facts about those specific readouts — **not** a verdict
that the panel lacks structure or "isn't the gate" (per the research stance: a marginal
being flat does not settle a structural object). Finer/other readouts of all three
objects remain open.

## 5. Next escalations (untested)
- **Full-resolution σ₁ concentration.** The label tests coarsen σ₁. The strongest
  form of "does the lift of S₃=0 concentrate" is whether a *fixed ℤ[ω] combination*
  of `eis(σ₁), eis(x_P), eis(x_Q)` is bounded (distinct/top-mass/N-bits), not a
  label MI. Not yet run.
- **Closure theorem (prove a panel solid).** Upgrade the §1–§3 scoped nulls to a
  Weil / Kohel–Shparlinski statement that bounded-degree lift readouts have
  MI = O(p^{−δ}) with d — the "prove the fence solid, equally valid" direction.
