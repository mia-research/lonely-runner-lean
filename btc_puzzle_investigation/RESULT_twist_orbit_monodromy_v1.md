# RESULT — `E[u⁴]` is consistent with full SU(2) monodromy (and excludes the CM/torus reduction)

*2026-07-26. Frozen run, reused SHA `7cde99fe…`. Grade: `[EMPIRICAL — out-of-sample, controls fired;
independent sign-off PENDING]` (the `experiment-designer` agent hit a session cap mid-audit — see §5;
the one concern it flagged is resolved object-level in §2). Signal path fully exact (rational moments,
no float). No leakage/ECDLP claim — this identifies a monodromy group.*

**One line:** the twist family's 4th moment `E[u⁴]` is **consistent with full SU(2)** Sato–Tate —
`E[u⁴] = 1/8` to a pooled `+0.00008`, **12/12** primes in the iid-SU(2) band at `p∈[823,2731]`. This
**excludes** monodromy reductions large enough to shift `E[u⁴]` — notably the CM/torus value `3/8`,
which PLANT-UNIF confirms is separable. It does **not prove** full SU(2): a reduction too small to move
`E[u⁴]`, or one visible only in higher moments or at larger `p`, is not excluded. The direction is
consistent with the `A_new`-channel picture that the twist frees the absolute angle toward Sato–Tate.

## §1 — Result (exact `E[u⁴]`, out-of-sample)

`u(a)=V(a)/(2i√p)`; `E[u⁴]=n·Σ_j R(j)²/(16p²(n−1))`, exact rational; iid-SU(2) band, `Rsim=4000`.
Full SU(2) predicts `1/8=0.125`; torus/CM predicts `3/8=0.375`.

| p | L | `E[u⁴]` | SU(2) band | in? | dev(1/8) |
|---|---|---|---|---|---|
| 823 | 138 | 0.12197 | [0.0946, 0.1596] | ✓ | −0.00303 |
| 907 | 161 | 0.13545 | [0.0955, 0.1566] | ✓ | +0.01045 |
| 967 | 151 | 0.11038 | [0.0955, 0.1580] | ✓ | −0.01462 |
| 991 | 168 | 0.13443 | [0.0965, 0.1557] | ✓ | +0.00943 |
| 1051 | 182 | 0.13163 | [0.0974, 0.1543] | ✓ | +0.00663 |
| 1303 | 208 | 0.11629 | [0.0996, 0.1518] | ✓ | −0.00871 |
| 1831 | 292 | 0.11723 | [0.1036, 0.1483] | ✓ | −0.00777 |
| 2143 | 348 | 0.11815 | [0.1047, 0.1468] | ✓ | −0.00685 |
| 2251 | 390 | 0.13340 | [0.1052, 0.1451] | ✓ | +0.00840 |
| 2503 | 426 | 0.12979 | [0.1070, 0.1451] | ✓ | +0.00479 |
| 2647 | 446 | 0.12750 | [0.1068, 0.1436] | ✓ | +0.00250 |
| 2731 | 448 | 0.12151 | [0.1077, 0.1448] | ✓ | −0.00349 |

**12/12 in the SU(2) band; 6/12 below 1/8 (symmetric); pooled L-weighted dev `+0.00008`.** Nowhere near
the torus/CM value 3/8. `E[u²]=n/(4p)≈1/4` throughout (forced; instrument). **Verdict: `E[u⁴]`
consistent with full SU(2), and the CM/torus reduction (3/8) is excluded — at these 12 primes, for this
moment. Not a proof of full SU(2) (higher moments / larger `p` untested).**

## §2 — The finite-p concern, and its resolution (the flagged issue)

The audit flagged: all **7 in-sample** `E[u⁴]` sat *below* 1/8 — is that a genuine sub-SU(2) reduction,
or a finite-p correction under full SU(2)? The two are separated by their **p-dependence**: a finite-p
correction shrinks with p; a real reduction is a constant offset.

**Resolved by the data:**
- The systematic sign **disappears out-of-sample** — 6 above / 6 below 1/8 (vs 7/7 below in-sample).
- **Convergence:** mean dev of the small-L half `+0.00003`, large-L half `−0.00040` — both negligible,
  no drift.
- **Extrapolation** of dev vs `1/√L` to `L→∞`: intercept `+0.0018 ≈ 0`.

⇒ the in-sample deficit was **finite-size**, and it **vanishes at the out-of-sample scale** — the
signature of genuine full SU(2), not a reduction. The concern is answered.

## §3 — What full SU(2) means here

The `χ₂(y)⊗χ_a` family is the twisted `A_new` channel. `A_new` is supersingular at `p≡3 mod4`
(eigenvalues exactly `√p·ζ`), but the **twist** `L_{χ_a}` deforms it. The data are consistent with the
**absolute** Frobenius angle `θ_a` being Sato–Tate-distributed (full SU(2)) on its one free angle
(`E[u⁴]=1/8` at these primes), and are inconsistent with the uniform/CM law (`3/8`). The **relative**
angle stays frozen at 120° (the forced CM structure, the effective 4-dim→2-dim reduction). This is the exact quantitative
form of `ANALYSIS_n1_cap_anew_channel_kronecker_route_v1.md §2`'s rigidity budget: *absolute rigidity
destroyed, relative rigidity (120°) survives.*

## §4 — Synthesis: what the tested axes show, and what they do not reach

| axis (statistic, scope) | result |
|---|---|
| arrangement, signed (odd χ on `V`, single-char, p≤2731) | null, out-of-sample |
| arrangement, magnitude (even χ on `\|V\|²`, single-char, p≤2731) | null, out-of-sample |
| 2-pt additive autocorr / 3-pt mult bispectrum | forced (exact) |
| value distribution, 4th moment `E[u⁴]` (p≤2731) | consistent with full SU(2); excludes 3/8 |

Across the axes tested, **no curve-specific structure was detected beyond the forced CM symmetry**
(`μ₃`+odd+purity+120° lock): the two free 2nd-order arrangement channels are null out-of-sample, the
other low-order arrangements are forced, and `E[u⁴]` is consistent with full SU(2) while excluding the
CM/torus reduction. **Each is a scoped result** — a specific statistic, at `p∈[823,2731]`, with a
stated power and (for the empirical rows) a grade of `[EMPIRICAL — SCOPED]`; none is a blanket claim of
"no structure" ([[feedback_negative_bias_enlarge_nulls_2026_07_17]]).

**What these tests do NOT reach** (so any remaining structure could still live here — neither found nor
excluded): joint/coupled objects (the additive-multiplicative cross statistics named in
`..._forced_landscape_v1.md`, the short-scalar regime), higher moments, and larger `p`.

## §5 — Provenance and the sign-off gap (disclosed)

- Instrument `twist_orbit_monodromy_run_v1.py` (C-NOFLOAT OK — moments exact `Fraction`/int; float only
  in the iid-SU(2)/uniform reference simulation). Freeze reused: `twist_orbit_spectrum_FREEZE_v2.json`,
  SHA `7cde99fe…`. Controls fired: C-FORCED (`E[u²]=n/4p`), C-CROSS (`nΣR²` == FFT `Σ|V|⁴`), PLANT-UNIF
  (center 0.375, separated from the SU(2) band ⇒ discriminator has power), C-NOFLOAT.
- ⚠ **Independent sign-off did NOT complete:** the `experiment-designer` agent terminated on a session
  cap (resets 20:00 Australia/Brisbane) after flagging exactly one concern (the finite-p null match),
  which §2 resolves object-level. This test therefore has a frozen prereg + validated controls +
  a resolved concern, but **not** the independent adversarial sign-off the signed/magnitude channels
  had. A retroactive sign-off is advisable after the session reset; the finding (12/12 in band, pooled
  dev `+0.00008`) is robust to it. Logged in `PREREG_twist_orbit_monodromy_v1_DEVIATIONS.md`.
- Prereg `PREREG_twist_orbit_monodromy_v1.md`; preview `monodromy_preview_v1.py`.
