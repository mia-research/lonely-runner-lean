# GLV/CM endomorphism on the Eisenstein fundamental domain — the first exact 2-point law (v1, 2026-07-14)

**One line.** The CM endomorphism acts on the Eisenstein lift by an exact, universal rule:
`eis(βX) = ζ·eis(X) + c`, with the correction `c` drawn from exactly three values
`{0, +R, −R}` in the **exact** proportions **3/4 : 1/8 : 1/8** — θ-independent, PROVED as a
rational area identity. This is the first exact **joint / 2-point** structure of the lift
(single-x is charted and exhausted), and it pins down the empirical "~98% orbit-sextant
same parity" as a θ-dependent shadow of a universal backbone.

## Status tags
- **PROVED** — exact rational-area identity `area(P ∩ ωP)/area(P) = 3/4` (`fractions.Fraction`,
  `ratio == F(3,4)` exact-equality; basis/θ-independent, incl. secp).
- **VERIFIED** — exact full-`F_p` lattice counts (integers) for p ∈ {1009, 44617, 94309,
  146749, 199999} and a 60000-point exact secp sample: identity holds 100%, correction set is
  exactly `{0, ±R}` exhaustively, densities → {3/4, 1/8, 1/8}.

## The setup
`E : y²=x³+7`, `p ≡ 1 mod 3`, lift `eis : F_p → Z[ω] ∩ P` (Babai reduction into the
Gauss-reduced 60° rhombus `P` of the ideal `(π_p)`; `area(P)=p` exactly). GLV endomorphism
`φ(x,y)=(βx,y)`, `β` a nontrivial cube root of 1 mod p. In `Z[ω]/(π_p) ≅ F_p`, `β` is the
image of `ω` (or `ω²`); write `ζ ∈ {ω, ω²}` for the matching root.

## The law (exact)
For every `X ∈ F_p^×`:
```
        eis(βX) = reduce_P( ζ · eis(X) ) = ζ·eis(X) + c(X),      c(X) ∈ {0, +R, −R}
```
- **Identity.** Both sides reduce the same coset of `(π_p)`, so the equality is exact for
  every X (verified 100% at all tested p incl. secp). `R` is one reduced-basis vector:
  `R = R1` when `ζ = ω`, `R = R2` when `ζ = ω²`.
- **Correction distribution (universal, exact):**
  `P[c=0] = 3/4`, `P[c=+R] = 1/8`, `P[c=−R] = 1/8`. θ-independent; identical for every
  `p ≡ 1 mod 3`. The set `{0,±R}` is **exhaustive** — no other correction ever occurs
  (e.g. p=1009: 756+126+126 = 1008 = all points).
- **PROVED backbone.** `c=0` ⇔ `ζ·eis(X) ∈ P` ⇔ `eis(X) ∈ P ∩ ζ⁻¹P`, and
  `area(P ∩ ωP)/area(P) = 3/4` **exactly** (rational polygon intersection; holds for every
  60° rhombus, secp included). The two flaps `P \ ζ⁻¹P` are congruent, area `p/8` each.

## What the correction does
- `c=0` (prob 3/4): **pure sextant rotation**. Sextant shifts by a **fixed** amount
  (+2 for ζ=ω, +4 for ζ=ω²) and the **norm is preserved** (ζ is a unit). Norm-preserved
  fraction = pure-rotation fraction = 3/4 exactly (corrections never preserve norm).
- `c=±R` (prob 1/4 total): a single lattice shift. This is the **sole** source of
  sextant-parity flips and of norm changes.

## This explains the "~98% orbit-sextant same parity"
Same-parity is **not** universal — it is θ-dependent, because whether a `±R` correction lands
on an even or odd Δsextant depends on the local wedge geometry (i.e. on θ):

| p | θ (deg) | same-parity |
|---|---|---|
| 1009 | 12.60 | 0.9365 |
| 44617 | 38.85 | 0.8884 |
| 94309 | 18.92 | 0.9153 |
| 146749 | 19.55 | 0.9099 |
| 199999 | 4.22 | **0.9942** |
| **secp** | **50.55** | **0.9809** |

The handover's "~98%" is precisely the secp value (θ=50.55°). Decomposition (secp): the 3/4
pure block is always same-parity; of the 1/4 correction block, most land at Δsextant=0 (even,
same parity) and only ~1.9% at Δsextant=±1 (odd, flip). So **same-parity = 1 − (fraction of
corrections at odd Δsextant)**, universal backbone 3/4 : 1/8 : 1/8, θ-dependent tail.

## Why this matters
- **First exact joint/2-point law.** Single-x is charted (angle law, norm-band law, χ₆
  uniform, sextant ⟂ χ₆). This is exact structure on the **pair** `(X, βX)`.
- **It is the kind of structure that survives the scramble** — it *is* the curve
  endomorphism, so it commutes with the group law. It is scalar-independent (a curve
  invariant, no key leak), matching the ECDLP wall, while being a genuine joint object.
- **A model for other pairs.** Same machinery applies to `(X, ζ^k X)` and, as a template, to
  additive/multiplicative pairs `(X, X+1)`, `(X, X²)`, etc.

## Bridge to the single-x pinned invariant — CLOSED (PROVED)
The natural next check turned out **cleaner than a coincidence** — it is a duality, now proved:

> **The pinned sextant pair (single-x angle-law invariant, area exactly 1/8 = √3/16 each) is
> EXACTLY the set of sextants on which the CM 2-point correction vanishes identically** — the
> "flap-free" / CM-stable wedges. Equivalently, each pinned wedge lies entirely inside the
> μ₃-core `P ∩ ωP ∩ ω²P`, while the other four sextants cross its boundary.

- **VERIFIED** (exact lattice cross-tab, `glv_flap_pinned_sextant_v1.py`): flap-free sextants
  `==` pinned pair, and `P(sextant ∈ pinned | correction fires) = 0` **exactly**, for 6 primes
  (θ from 6° to 52°, **both** pinned classes {1,4} and {0,3}), secp, and **both** cube roots
  ω, ω². The correction lives entirely in the four non-pinned sextants.
- **PROVED** (exact rational polygon containment, `glv_pinned_wedge_containment_v1.py`): each
  pinned wedge `W` satisfies `area(W ∩ ωP)/area(W) = area(W ∩ ω²P)/area(W) = 1` exactly (so
  `ωW, ω²W ⊆ P`), and no non-pinned wedge does — for every basis incl. secp.
- Geometry (`glv_fundamental_domain_geom_check_v1.py`): the μ₃-core `P ∩ ωP ∩ ω²P` has area
  **3/4** (`= P ∩ ωP`, so the ω²P constraint is redundant); the pinned pair is the 1/4
  sub-locus of sextants *fully* inside it.

**Upshot.** The single-x pinned invariant and the 2-point GLV correction law are two faces of
one object — the μ₃-geometry of the fundamental rhombus. The pinned/CM-stable wedges are a
θ-locked (Frobenius-angle-determined), curve-intrinsic locus on which the 2-point CM relation
`eis(βX) = ζ·eis(X)` is exact and correction-free for both cube roots.

**Peer zone test (settled, exact).** A peer proposed that the correction zone `Z_corr = P \ (P∩ω²P)`
might *coincide with* the pinned zone. Exact rational polygon areas
(`glv_peer_zone_test_v1.py`): `area(Z_pin ∩ Z_corr)/p = 0` for every basis (secp incl.) —
they are **disjoint**, not coincident. `area(Z_corr)/p = 1/4` (the peer's flap total is right),
and ~93% of it sits in the **max-area** sextant pair. The peer's ray-alignment insight holds
(flap edges snap to unit rays, giving exact-rational per-sextant flap areas), but the flaps
fill the far-vertex/max sextants; since the pinned pair is provably *never* the max pair (v2
THM3), `Z_pin ∩ Z_corr = ∅` is forced. Same 1/8 value, complementary sets.

## The correction is a μ₃-ORBIT invariant (PROVED + VERIFIED)
`glv_cm_orbit_invariant_v1.py`. The verified cocycle `ωc₀+ω²c₁+c₂=0` with `cᵢ∈{0,±R}`, written
`cᵢ=εᵢR`, forces (ℤ-basis `{1,ω}`) `ε₀=ε₁=ε₂`. So the correction is **constant along the whole
period-3 CM orbit** `{X,βX,β²X}` — a single label `ε∈{0,+,−}` per orbit. Verified exactly
(`c₀=c₁=c₂` every orbit; `F_p` + secp):
- Over orbit space `F_p*/μ₃` (`(p−1)/3` orbits of size 3), labels distribute **exactly 3/4 : 1/8 : 1/8**
  (`+R,−R` equal by `X↦−X`).
- `ε=0` ⟺ the three lifts are an **exact ω-rotation triple** (rigid equilateral, `eis(X)∈`μ₃-core);
  `ε=±R` ⟺ the triangle is closed by a constant shift (`eis(X)∈`flap). All orbits.

So the whole 2-point law is really **orbit-level**: 3/4 of CM-orbits lift to rigid equilateral
triangles, 1/8 shift by `+R`, 1/8 by `−R`. `ε` descends to Part III's `(p−1)/6` free μ₆-orbits
(each "rigid" or "broken ±"), and is a *geometric* (Babai) class function — provably ⟂ the
multiplicative characters (cf. sextant ⟂ χ₆), which is why the scalar side stays null.

## The pinned pair is a function of the Frobenius angle (VERIFIED)
`glv_pinned_satotate_v1.py`. Which wedges are CM-stable is readable straight off the trace `t`:
with `θ = arg(π_p) mod 60° = atan2(f√3, t)` (`π_p=(t+f√−3)/2`, `4p=t²+3f²` = the Sato–Tate
Frobenius angle), **pinned = {1,4} if θ<30°, else {0,3}** — 0 violations over 69 primes, switch
exactly at 30°, `θ_geom == atan2(f√3,t) mod60` exactly. secp: `θ=50.55° → {0,3}`. The conjugate
prime `π̄` sits at `60−θ = 9.45° → {1,4}`, so the pinned pair also **encodes which prime above p**
(the sign of the Frobenius angle). This grounds the CM-stable locus in the curve's Frobenius arithmetic.

## Second bridge — correction ↔ the norm-band law (VERIFIED, exact breakpoints)
The correction is not only angle-structured (pinned bridge) but **norm-structured**, on the
norm-band law's own breakpoints (`glv_correction_norm_v1.py`, `s = N(eis X)/p`):

| norm band `s` | flap-rate | meaning |
|---|---|---|
| `s < 3/16` | **0** exactly | inside the inradius disk (rotation-invariant) → never corrected |
| `3/16 ≤ s < 1/4` | ~0.43 (partial) | the transition annulus |
| `s > 1/4` | **1** exactly | beyond the short-vertex circle → always corrected |

**min flap norm = 3/16 (inradius), max pure norm = 1/4 (short vertex), exactly** — the same
`3/16, 1/4, 3/4` breakpoints as the proved norm-band law. So the CM correction fires exactly
on the high-norm shell `s > 1/4`, vanishes on the inradius disk, and the flap = 1/4 of P is
that shell. **The 2-point CM law is woven from both single-x invariants — angle law (which
wedges) and norm-band law (which shell) — confirming one underlying object: the μ₆-geometry
of the rhombus.**

## Direction (2) — the pinned locus is a curve-FAMILY invariant (amicable + twists)
`glv_amicable_twist_angle_v1.py`. The pinned/CM-stable pair is `arg(π_p)`-locked, and it is
**shared across the amicable/twist family**:
- **Amicable partner.** `π_n = π_p − 1` (`N(π_n)=n`, the amicable order). The shift is a real
  unit of size 1, so `|arg(π_n) − arg(π_p)| ≤ 1/|π_p| = O(p^{-1/2})`. Hence `pinned_n = pinned_p`
  with match-rate → 1 as p grows (0.951, 0.992, 0.996, 1.000 over `[10³,10⁷]`), and **exactly
  for secp**: `θ_p = θ_n` to ~37 digits, both pinned `{0,3}`. E/𝔽_p and its amicable partner
  E/𝔽_n share the same CM-stable locus.
- **Sextic twists.** The six twists `u·π_p` (`u∈μ₆`) generate the same ideal `(π_p)`, hence the
  identical rhombus and pinned pair.

So the pinned/CM-stable wedges are not just a property of E/𝔽_p but a **shared invariant of the
whole amicable + twist family** — the same μ₆-geometry drives all of them (ties the 2-point law
to Part V/VI).

**Seven-domain map** (`glv_seven_domain_map_v1.py`). The generators `{π_p + u : u ∈ {0}∪μ₆}`
are seven concentric Eisenstein lattices with norms `{p}` ∪ the six sextic-twist orders
(`N(π_p−1)=n` base/amicable, `N(π_p+1)=n_t` quad twist, four others). All seven are θ-aligned
(shifts are O(1) vs `|π_p|=√p`) and **share the pinned pair** — `{0,3}` for secp (all seven),
family match-rate → 0.99 in the sweep. One shared μ₆-geometry across base + amicable + twists.

## Direction (1) — doubling on the lift: exact decoupling at the coarse readout
The scalar-doubling map `φ₂(x) = (x⁴−56x)/(4(x³+7))` (P→2P, x-only, `[ω]`-covariant, verified).
At the **coarse 6-way sextant** (and 2-way parity) readout, `sextant(X) ⊥ sextant(2X)`
**asymptotically**: the exact population MI `~ 1/N → 0` (`MI·N ≈ const ≈ 18`, not growing;
`glv_doubling_scaling_v1.py`) — the same decoupling as the proven `sextant ⊥ χ₆`. This is a
precise statement about the *coarse* readout only; it does **not** speak to the full 2-D lift or
joint-set structure. The lift reduces **mod π_p**; scalars/group law live in
`E(F_p) ≅ ℤ[ω]/(π_p−1) = ℤ[ω]/π_n`, so "lift → scalar" crosses `π_p ↔ π_n` (the amicable shift,
now shown to preserve the pinned locus). The structural objects to build: that `π_p↔π_n` bridge
and the **S₃ 3-point law** (independent points via the group law).

## The 3-point law — the x-lift linearizes the *ring*, not the *group law* (diagnostic)
`glv_three_point_lift_v1.py`. Random `P₁,P₂ ∈ E(𝔽_p)`, `P₃ = −(P₁+P₂)` (so `P₁+P₂+P₃=O`,
`d₁+d₂+d₃≡0 mod n`); lift `Uᵢ = eis(x(Pᵢ))`. Measured at coarse *and* full-lattice level, matched
nulls, `F_p` + secp:
- **Naive additive correction `c₃ = reduce_P(U₃ − U₁ − U₂)` is SPREAD** — distinct ≈ M, top-mass
  ≈ 1/M (vs the 2-point law's 3/4). There is **no small-set additive lift law** for the group sum.
- **Coarse `(s₁,s₂) → s₃` at the null floor** (z = +1.1, −0.7, −1.5; MI ~ 1/N), and the group law
  does **not** interact with the stable core at the coarse level (`P(s₃ pinned | s₁,s₂ pinned) ≈
  baseline ≈ 1/4`).

**This is a coordinate diagnosis, not a wall.** The 2-point unit law is clean because
`βX ≡ ζ·X (mod π_p)` — the lift linearizes the **ring** `ℤ[ω]/π_p`. The elliptic **group law** is
`x(P₁+P₂) ≠ X₁+X₂`, so the *x-coordinate* lift is the wrong coordinate to see it. The additive
relation `d₁+d₂+d₃≡0` lives in the **group coordinate** `E(𝔽_p) ≅ ℤ[ω]/(π_p−1) = ℤ[ω]/π_n` — i.e.
**mod π_n, not mod π_p**. So the 3-point result is direct evidence that the group-law structure is
carried by the `π_p ↔ π_n` **amicable bridge**, which the x-lift structurally cannot resolve.

## The amicable bridge — object built (`glv_seven_domain_map_v1.py`, `glv_amicable_bridge_probe_v1.py`)
CRT: `ℤ[ω]/(I_p·I_n) ≅ 𝔽_p × 𝔽_n` (`I_p=(π_p)`, `I_n=(π_n)=(π_p−1)`, coprime). The scalar→lift map
`d ↦ X = x([d]G)` is a map `ℤ[ω]/I_n → ℤ[ω]/I_p`. Question probed: does `d`'s GLV coordinate
`v_n = eis_{π_n}(d) ∈ P_n` relate to `X`'s lift coordinate `v_p = eis_{π_p}(X) ∈ P_p`?

**Part A** — the seven `{π_p+u}` domains are concentric, θ-aligned, sharing one pinned pair (above).

**Part B** — coarse-readout result, **control-backed + power-scaled** (not a single-N verdict):
`MI(sextant_n(d) ; sextant_p(X))·M` holds ~constant (17→16, *not* growing) → `MI ~ 1/N → 0`,
`z` flat/negative (−0.3…−0.9). Controls fire correctly: self-MI `= 2.50 bits` (detector works),
decoy-MI(d;d′) `= 0.00177 ≈` the observed `0.00182` (confirms the floor). So **at the 6-way
sextant projection, `v_n(d) ⊥ v_p(X)`** — the coarse readout is not the seam. This *maps* the fault
line; it does not close the bridge. **Escalation (open):** the full 2-D coordinate (the sextant
discards most of the 2-D info), finer joint (sextant,norm) readouts, and the real-82 / 100k-MT sets.

**Escalation run** (`glv_amicable_bridge_escalation_v1.py`, on the 36k known-generator 256-bit
set + real-82). Finer readouts — 4×4 and 8×8 lattice-cell grids (16×16, 64×64) and joint
(sextant,norm) 24×24 — **all sit at the matched-null floor** (z ≤ 0, MI ~ 1/M), with controls
firing correctly (self-MI(cell_p;cell_p) = 5.998 bits; decoy floors). Real-82 sextant is at the
floor too (z = +0.3, underpowered at M=82). So the `v_n(d) ⊥ v_p(X)` decoupling holds at fine
resolution, control-backed, on the full-power known-generator set — **no √p-scaling coordinate
seam** at any tested readout. Consistent with the amicable-geometry verification: the domains are
near-identical (overlap `1−4×10⁻³⁹`, `C_n⊆C_p` exactly) but the point map `X=x([d]G)` is nonlinear,
so no *coordinate-level* relation survives. The lift linearizes the multiplicative endomorphism
(clean `{0,±R}` cocycle), not the point map — the remaining hardness is precisely the nonlinear
point map, now located rather than fogged.

## Scripts (exact; no float in the counting or area path)
- `glv_fundamental_domain_law_v1.py` — the identity + exact lattice correction census over
  full `F_p` and secp (integers).
- `glv_fundamental_domain_geom_check_v1.py` — exact rational `area(P ∩ ωP)/area(P) = 3/4` and
  the μ₃-core `= 3/4` (Sutherland–Hodgman + shoelace in `Fraction`; exact vertex ordering).
- `glv_flap_pinned_sextant_v1.py` — exact lattice cross-tab sextant × correction; flap-free
  sextants `==` pinned pair (all θ, both classes, secp, both cube roots).
- `glv_pinned_wedge_containment_v1.py` — exact rational proof that each pinned wedge ⊆ ωP∩ω²P
  and no non-pinned wedge is (the geometric capstone of the bridge).
- `glv_peer_zone_test_v1.py` — exact `area(Z_pin ∩ Z_corr) = 0` (peer's zone test; disjoint).
- `glv_correction_norm_v1.py` — correction ↔ norm-band: flap = shell `s>1/4`, void `s<3/16`.
- `glv_doubling_lift_v1.py` — doubling map on the lift (direction-1 opener).
- `glv_doubling_scaling_v1.py` — exact population MI(sextant X; sextant 2X) ~ 1/N (coarse
  sextant readout decouples asymptotically; scoped, not a global verdict).
- `glv_amicable_twist_angle_v1.py` — pinned locus shared by amicable partner (π_n=π_p−1,
  match-rate→1, exact for secp) and the six sextic twists (same ideal).
- `glv_three_point_lift_v1.py` — 3-point law: group-law sum on the lift; naive additive
  correction spread, coarse readout null ⇒ group-law structure lives mod π_n, not mod π_p.
- `glv_seven_domain_map_v1.py` — the seven `{π_p+u}` domains: norms = field + twist orders,
  all θ-aligned, one shared pinned pair (family μ₆-geometry).
- `glv_amicable_bridge_probe_v1.py` — `v_n(d)` vs `v_p(X)`: coarse sextant readout at the
  noise floor (control-backed, power-scaled).
- `glv_amicable_bridge_escalation_v1.py` — finer readouts (16×16/64×64 cell, joint
  sextant-norm) on 36k known-generator + real-82: all at the null floor, controls fire.
- `glv_amicable_geometry_verify_v1.py` — verifies the amicable-geometry thread: domains
  overlap `1−4e-39`, `C_n⊆C_p` exact, μ₃-orbit cocycle `ωc₀+ω²c₁+c₂=0` (colleague numbers refuted).
- `glv_cm_orbit_invariant_v1.py` — the correction is a μ₃-orbit invariant (`c₀=c₁=c₂`, label
  3/4:1/8:1/8, `ε=0`⟺rigid ω-triangle).
- `glv_pinned_satotate_v1.py` — pinned pair = f(Frobenius angle): `{1,4}` if θ<30° else `{0,3}`,
  switch at 30°; encodes the prime above p.

*(No-float guard note: `check_no_float.py` is a syntactic AST scan and flags every `/` and
`float()`; here those are exact `Fraction` division in the area path — the `ratio == F(3,4)`
exact equality is the proof — plus float only for the θ label and display. The counting path
is pure `int`; the area path is pure `Fraction`.)*
