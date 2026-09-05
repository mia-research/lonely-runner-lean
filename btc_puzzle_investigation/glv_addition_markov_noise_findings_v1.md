# Addition-rounding Markov law + noise-separation (findings v1, 2026-07-14)

From an independent exploration (the user's `9stated.py` / `secp_markov_sampler.py`):
the 9-state Babai-rounding chain of `eis(x(kG)) + eis(x((k+1)G))`, its transition
spectrum, and the additive correction `V`. Audited here with the scaling
discriminator + distribution controls. Scripts: `glv_addition_markov_audit_v1.py`,
`glv_noise_separation_v1.py`, `glv_lambda2_settle_v{1,2,3}.py`. Exact integers in the
lift/state/V path; float only in eigenvalue/MI statistics vs matched nulls.

## 1. The 36:6:1 state law = tensor square of the flap constant  **[PROVED + VERIFIED]**
The rounding state `(c1,c2)` of `z1+z2` (two independent uniform-in-P lifts) has
distribution **`(3/4:1/8:1/8) ⊗ (3/4:1/8:1/8) = 36:6:1 : 6:1 : …`**:
- Per coordinate: sum of two uniforms on `[-½,½]` is triangular on `[-1,1]`; rounding
  gives `∫_{-1/2}^{1/2}(1-|s|)=3/4` (c=0), `∫_{1/2}^1(1-s)=1/8` (c=±1). **[PROVED]**
- P is a parallelogram ⇒ basis coords independent ⇒ 2-D = product. **[PROVED]**
- **[VERIFIED]** curve (0.5687) = random-field-elements (0.5604) = predict (0.5625),
  all 9 states. The equality with random x confirms the law is **pure lift
  self-convolution, group-law-independent** — a clean unification (the endomorphism
  flap constant 3/4:1/8:1/8 is the per-coordinate marginal of the addition rounding),
  but not a scalar leak.

## 2. Transition memory λ₂ — G is typical among generators (bug-corrected)  **[VERIFIED]**
Consecutive-`kG` chain: λ₂ ≈ 0.34, gap 0.66 (user's finding). Audit ladder:
- vs shared-term controls (audit_v1): REAL 0.3398 vs 0.3318/0.3335 — within noise.
- scaling to N=90k (settle_v1/v2): the gap `λ₂_REAL − λ₂_iid` is a **stable ~0.0047,
  not growing**; z climbs only because control sd shrinks — not leak-scaling.
- **settle_v3 RETRACTED — control bug.** v3 built control chains with INDEX
  arithmetic (`j+=h; if j>n: j-=n`) that wrapped at the affine count `n` instead of
  the group order `n+1` and mishandled `O`; REAL(G) (N<n, no wrap) was clean but every
  control was noise-inflated. Its "19/40, z=−0.20" verdict and its `+0.21` tail were
  ARTIFACTS (see below).
- **investigate_v4 (bug-free point-walks `S,S+H,…`; group order 99667 is PRIME ⇒ no
  small-order steps ⇒ the v3 tail was purely the wrap bug):** iid_mean 0.33485 (sd
  0.0037). `gap(G)` = **+0.0041 ± 0.0019** (8 starts) — real, reproducible, ~2σ>0.
  Full-order-generator gaps (60 steps): mean **+0.0013**, sd **0.0044**; `gap(G)` at
  **48/60, z = +0.64** — high side but **not a significant outlier**.
- **Reading:** there is a **small, reproducible positive λ₂ gap (+0.0041)** for the
  generator orbit vs i.i.d. — real orbit structure. Across 60 full-order generators G
  sits at z=+0.64 (48/60), i.e. not distinguished from a generic generator AT this
  observable/N/prime. Bounded to: λ₂ observable, 60 generators, N=60k, p=100003 (prime
  order). Whether a finer transition-matrix feature (specific entries, not just λ₂) or
  other primes distinguish G is OPEN — not a settled "no fingerprint".

## 3. The two-point correction V — in the closure's bilinear gap
`V = eis(x(P+Q)) − folded(eis(x_P)+eis(x_Q))` is a function of three coordinates, so
it lies OUTSIDE the single-sum closure theorem (`glv_closure_theorem_v2.md`, the named
bilinear gap) — a genuinely uncovered region. Probed so far (noise_separation_v1,
M=40k independent pairs, p=100003):
- V spreads over the domain (distinct ≈ M, `|V|²≤3p`, mean `p/3`).
- `sextant(V)` and `normbucket(V)` vs `a%6`, `(a+b)%6`, `(a−b)%6`: these **6 coarse
  projections** flat (z in [−1.3,+0.8], no √N growth, controls clean). Scoped to these
  projections/labels/N — the bilinear gap is not exhausted (finer projections,
  structured pairs, multi-key untested).

## 4. What these specific probes showed (and what stays open)
Positive facts established this pass: the exact **36:6:1 tensor-square** state law, the
**4-cell bridge quantization**, and a **reproducible +0.0041 λ₂ orbit gap**. At the
probes tested — the λ₂ observable, 6 coarse projections of `V`, mod-`m` targets,
p=100003 — the scaling discriminator + distribution controls did not separate a scalar
signal; each is scoped to its probe, **not** a statement that the objects are
structureless. Untested / open: finer transition-matrix features (specific entries, not
just λ₂), finer & other projections of `V`, structured pairs `Q=[m]P` (NB later found
closure-covered via the m-division polynomial), the **multi-key joint SET**, secp scale,
non-mod-`m` targets. `glv_noise_separation_v1.py` (scaling z-trajectory + matched
control per candidate readout) is the tool to point at these.
