# Amicable-slippage probe — field-lift(X) vs scalar-lift(d) (v1, 2026-07-17)

**Question.** The last live candidate for the user's "not obviously linked interference": secp is an
amicable pair (`n = N(π_n)`, `π_n = π_p − 1`), so the scalar ring `ℤ/n = ℤ[ω]/(π_n)` and the field
ring `F_p = ℤ[ω]/(π_p)` have CM rhombi that **nearly coincide**. Does the near-coincidence leave a
residual coupling between the FIELD lift `eis_p(X_d)` (public) and the SCALAR lift `eis_n(d)` (a
function of the secret `d`, a *different* function of `d` than the band decomposition)? If public
`eis_p(X_d)` predicted `eis_n(d)`, that would be a leak.

Script: `lift_amicable_slippage_v1.py`. Dataset: **36k `constructed_keys_fullrange_v1.csv`, bits=256
stratum, 21,000 keys** — chosen because `eis_n(d)` only reduces non-trivially for `d ≳ √n ~ 2¹²⁸`;
small keys give `eis_n(d)=(d,0)` (vacuous). Signal path exact int; float only in MI/corr/z vs matched
shuffle nulls.

## Verified construction  `[VERIFIED exact]`
- Scalar-side ideal `(π_n)` reduced basis: `N(R1n) = N(R2n) = n` exactly.
- Slippage vs field-side: `R1p − R1n = (0,1)`, `R2p − R2n = (1,1)` — the two lattices differ by **one
  unit per coordinate** (~2⁻¹²⁸ relative). Matches the known amicable geometry.
- Non-vacuous: `eis_n(12345) = (12345,0)` (trivial) but `eis_n(~n/4)` reduces to `|u| ~ 2¹²⁴`. On the
  bits=256 stratum `eis_n(d)` is a genuine reduction — the reason the 36k set (large keys) is required.

## What the measurements were  `[EMPIRICAL, controls fired]`
Instrument validated every run: planted `f=0.30 → z=868`, `f=0.05 → z=34`; random `z=−0.3`. These are
magnitude readings against a raw-`X mod 8` baseline, NOT verdicts about mechanism.

1. **Direct geometric coupling (A).** Pearson of field-lift vs scalar-lift components — `u_p~u_n`,
   `v_p~v_n`, `s_p~s_n`, cross terms — all `|rho| ≤ 0.007`, `|z| ≤ 1.4`. `sextant_p × sextant_n` MI:
   `I_c=−0.0004`, `z=−1.4`. (Reads as: no linear/low-order geometric covariance above the ~2% floor.)
2. **Leak framing (B).** Public `eis_p(X)` features {sextant, flap, sign(xy), s-bin, u-sign} →
   `eis_n(d)` targets {sextant_n, s_n-bin, u_n-sign, u_n-bin}: whole grid `|z| ≤ 2.3`, no feature
   beats the raw-`X mod 8` baseline; the top cell does not power-ramp (z non-monotonic across N, no
   plateau — contrast the planted control that ramps to z≈34).
3. **Slippage isolate.** `δ(X) = eis_p(X) − eis_n(X)` (the SAME value reduced under BOTH lattices =
   purely the `(0,1)/(1,1)` slippage effect): features `sign(δ_u)`, `|δ|`-bin → `|z| ≤ 1.2`, at/below
   the raw-X baseline for the two `δ`-features I constructed.

## What this does and does NOT establish  (read this literally)
- **Establishes (magnitude, scoped):** in the specific geometric features above (sextant/flap/norm/sign
  of each lift, and two functions of the slippage `δ`), any coupling between `eis_p(X_d)` and `eis_n(d)`
  on the 21k bits=256 keys is **below ~2% leak strength**. That is a bound on those features at that
  floor. Nothing more.
- **Does NOT establish** — and I am not claiming: that the two lifts are "independent"; that the ECDLP
  "scramble survives" the reduction; that the amicable channel is dead; that the three lenses this
  session "agree the curve is independent of the scalar." Those are enlargements of scoped nulls into a
  closure and are **not** supported. This is an empirical null with firing controls, **not** an
  analytical result. Only a rigorous proof closes an avenue.
- **The unexploited object.** The slippage is *exactly* `(0,1)/(1,1)` — a precise algebraic fact that
  this probe did **not** connect to `d`. The null measured the magnitude of a few coordinate features;
  it did not exhaust functions of `δ`, sub-2% strength, other bit-strata, the symmetry-type channel, or
  any structural (non-statistical) use of `(π_p−1)(π_n−1)`. Whether the exact slippage forces the
  reductions to decouple, or admits a regime where they don't, is an **open proof question** the null
  leaves entirely untouched — it is a reason to look harder at the algebra, not a reason to stop.

*Grades: VERIFIED (exact construction: N(R1n)=N(R2n)=n, slippage (0,1)/(1,1), non-trivial reduction) ·
EMPIRICAL (scoped magnitude null, controls fired). No analytical/closure grade is claimed anywhere here.*
