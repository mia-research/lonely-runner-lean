# BTC Puzzle — Findings v3 (the missing synthesis)

Date: 2026-07-09. The WPZ coordination step (adjudicate WP1–WP8 → v3) was never
executed; this is that synthesis, written after actually reading every WP result
JSON + log, the `scripts/` and `farm/` code, and the v1–v6 plans. Methodology
(§0 of v2) stands; not re-derived. Conditional-negative phrasing throughout.

## §1 — What each work package actually found (with control status)

| WP | what it tested | control fired? | verdict |
|---|---|---|---|
| WP1 | `n·Q` near-miss identity; recover true `n` from small residual `r` | **yes** (z=6.1, bands 16–20) | identity REAL & detectable at small N; coarse public scores do NOT separate true-n at N∈[8,120]. **Deeper large-N test (real DL-distance oracle / deeper k-grid) NEVER RUN.** |
| WP2 | joint ML classifier `public → n` (map ceiling), 20k, 406 feats | **no** | INCONCLUSIVE / underpowered; discarded, not a negative. MLP real 0.0143 vs matched-null 0.0071 never re-run at power. |
| WP3 | small-N exact ledger | n/a | exact bookkeeping only. |
| WP4 | marginal n-priors vs matched-multiset null (82 real keys) | no (attack_valid=false) | prior only; real-key z-scores null (prime-rate z=−1.37, φ=2r z=0.0). Constructed set IS the null. |
| WP5 | GLV split `(d1,d2) mod n` vs n | yes | ΔMI ≈ 0 → null (structure diagnostic, uses known d). |
| WP6 | 12 candidate-distinguisher families (x_mod, y_mod, kron, gcd, …) | **yes** (p_γ=0.02) | powered; apparent `x_mod` signal **VERIFIED CONFOUNDED** by n's magnitude/divisors (perm-Bonferroni p=1.0) → null. |
| WP7 | feature-family battery (spectral, compression, …) | yes (spectral) | **only `spectral` ran → null. Remaining families NEVER RAN.** |
| WP8 | exotic two-stage (trace probe, Bragg sweep, pairing) | partial | stage-2 Bragg top-1% = 0.0096 ≈ baseline (null); pairing trivial (e(dG,G)=1); **CRASHED at Tate toy.** |

## §2 — Surviving signals after all 5 adjudication checks

**None passed.** The two the WPZ brief flagged as most likely both fail on read:
- WP6 `x_mod` — dies on check 4 (right null): the naive KS p is confounded by
  n's own structure; permutation-Bonferroni p = 1.0.
- WP4 marginal-n prior — attack_valid=false + real-key z-scores within noise;
  it is a prior on the *constructed* set, which IS the null, so it cannot show
  creator selection.
Consistent with the v5 conclusion (integer-selection avenue is data-starved at 82
real keys) and with this session's powered leak-null on the 100k.

## §3 — This session's additions (2026-07-09)

- **NEW & real:** the 2019 consolidation tx `17e4e323…` (21 puzzle inputs, one
  signer) shows **nonce heterogeneity** — 4/21 plain RFC6979, 10/21 randomized,
  the 4 clustered at adjacent input pairs. Not low-R grinding (r ~uniform). A
  genuine, previously-unextracted forensic regularity in public data.
  (`nonce_lattice.py`, `nonce_variant_id.py`.) NB: base nonce recovery already
  existed in `scripts/nonce_recover.py`; only the RFC6979-split is new.
- **Powered leak-null on 100k** (`leak_scan_100k.py`, `linear_leak_100k.py`): the
  map `d→(X,Y)` leaks no scalar bit — single-bit, N-scaling, and full-256-bit
  linear probe all at chance; controls pass. (82-key tests had no power; this
  settles it.)
- Curve algebra laid out exactly: CM j=0, `4p=t²+3f²` verified, twist has
  `3²·13²`. Intrinsic stats provably uniform by the Weil bound.

## §3b — Un-run tests now COMPLETED (2026-07-09)

**WP1 deep `n·Q` test — RESOLVED, no leverage (`wp1_deep.py`).** The identity
`n·Q − (n+k)·A = r·G`, `r = n·D − (2^{N−1}k mod n)`, holds exactly (15/15 sampled).
The deferred question was whether a real DL-distance oracle (not WP1's coarse
`min_x` proxy) separates/recovers the true n. Measured the actual residual: **|r|
scales as ~1.00·N** (median r-bits ≈ N−10) — essentially full-size, always ABOVE
the plain-kangaroo exponent N/2 (leverage only at N=16, a small-N artifact).
`|r|<2^40` only for N≤~48 (already trivially small keys). **Conclusion:** the
identity is an exact re-parametrization whose detectable quantity is full-size, so
recovering the key through it costs ≥ plain interval search — NO advantage. This
explains WP1's null at the root: not a weak instrument, the target is full-size.
Bounded-negative, now with the mechanism.

**WP2 map-ceiling at power — RESOLVED, null with a FIRING control (`wp2_power.py`).**
GBM (HistGradientBoosting) predicting n / n_is_prime / n mod 3 / n mod 2 from the
64 public X,Y bytes, 50k rows. Real accuracy = baseline = shuffled-null for every
target (n: 0.0050 vs 0.0039; n_is_prime: 0.6903 vs 0.6904; n mod 3: 0.373 vs 0.380;
n mod 2: 0.654 vs 0.654) → no nonlinear leak. **Planted-leak control fires**
(strength 0.5 → 0.749, 1.0 → 1.000), so the detector has power (the original WP2
control never fired — that null was rightly discarded; this one is believable).
Caveat: control floor ~0.4 (targets are majority-imbalanced, so a planted signal
must beat the majority class to register); bounded to leaks above that floor.
Together with the powered single-bit + linear probes (§3), the map d→(X,Y)→n shows
no practically-detectable leak.

## §4 — The genuinely un-run tests (the answer to "missed opportunities")

Ranked. These are things actually never executed, not re-confirmations:

1. **WP7 remaining feature families.** Only `spectral` of the planned battery ran.
   `compression`/Kolmogorov-proxy and the others are literally untested on the
   100k. Concrete, powered, already-scaffolded (`farm/wp7_run.py`) — just finish it.
2. **WP1 deeper `n·Q` test at large N.** The one curve-structural identity that
   showed a real small-N effect. Needs a proper k′-grid depth and/or a real
   DL-distance oracle at N≫20; deferred for runtime, never done. This is the most
   principled remaining probe (algebraic, not a fishing feature).
3. **WP2 map-ceiling at power.** The MLP beat the matched null (0.0143 vs 0.0071)
   but the control didn't fire → discarded. Re-run with a firing control before
   accepting the null.
4. **WP8 stage-2 / pairing** — re-run without the crash (fix the non-invertible
   modulus in the toy), though the pairing avenue is a-priori trivial.

## §5 — Highest-value next action (one pick)

**Finish WP7's family battery, then run the WP1 deep test.** Rationale: WP7 is the
cheapest genuine gap (scaffold exists, just un-run families) and WP1 is the
highest-principle one (a real curve identity with a real small-N effect, left
unfinished). Both are "tests we said we'd run and didn't," which is exactly what
the brief asked to surface — as opposed to inventing new fishing probes, which the
82-key data can't power and the 100k has already nulled broadly.
