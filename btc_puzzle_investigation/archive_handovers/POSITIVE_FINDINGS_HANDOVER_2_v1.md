# secp256k1 — Positive Findings Handover 2: the Lift-Geometry Programme (v1, 2026-07-14)

A second, live compendium — a **launching pad** to extend over the next few sessions. It records
the exact structure found on the Eisenstein lift `eis : 𝔽_p → ℤ[ω]∩P` and the bridges it opens to
the curve's own arithmetic. Companion to (does not supersede) `POSITIVE_FINDINGS_HANDOVER_v3.md`;
full detail + 16 scripts in `glv_fundamental_domain_law_v1.md`. All arithmetic exact (`Fraction`/`int`).

### Stance (read first)
We are **mapping a fence and looking for its gate**, not describing a wall. The discrete log is
**currently hard**, not impossible — that is the object under inspection, not a verdict. Every
"null" below is a **scoped result about one readout we inspected**, with its control row checked;
it tells us *which panel of the fence to inspect next*, and is never a declaration that a panel is
closed. Positive, exact structure leads. Open items are invitations, phrased as such. (Per project
`CLAUDE.md` research stance + `feedback_curve_positive_framing_2026_07_14`.)

### Notation
`β` = GLV cube root of 1 mod p (`β≡ω²` mod `π_p`); `ζ∈{ω,ω²}` its lift; `P` = Gauss-reduced 60°
rhombus of `(π_p)`, area `p`; `R` = a reduced-basis vector; `s = N(eis X)/p ∈ [0,3/4]`.

---

## 1. The spine — the 2-point CM law  **[PROVED]**
For every `X`: `eis(βX) = ζ·eis(X) + c`, with the correction `c ∈ {0, +R, −R}` **exhaustively**, in
densities **exactly 3/4 : 1/8 : 1/8** (θ-independent). `area(P ∩ ωP)/area(P) = 3/4` as an exact
rational (basis-independent, secp included). Pure rotation (3/4) preserves norm and shifts the
sextant by a fixed amount; the `±R` flap (1/4) is the sole source of norm change / sextant-parity
flips — which is exactly the empirical "~98% orbit-sextant parity", now derived.
*(`glv_fundamental_domain_law_v1.py`, `_geom_check_v1.py`.)*

## 2. The correction is a μ₃-ORBIT invariant  **[PROVED + VERIFIED]**
Along the period-3 orbit `{X, βX, β²X}`, `c₀=c₁=c₂=εR` — one label `ε∈{0,+,−}` per **orbit** (the
cocycle `ωc₀+ω²c₁+c₂=0` plus the ℤ-basis `{1,ω}` forces it). Over orbit space `𝔽_p*/μ₃` (`(p−1)/3`
orbits) the labels are **3/4 : 1/8 : 1/8**; `ε=0` ⟺ the three lifts form a **rigid ω-rotation
triangle** (`eis X ∈ μ₃-core`), `ε=±R` ⟺ the triangle is closed by a constant shift (`eis X ∈ flap`).
`ε` descends to the `(p−1)/6` free μ₆-orbits (Part III), and is a **geometric (Babai) class
function** — structurally independent of the multiplicative characters (`sextant ⟂ χ₆`).
*(`glv_cm_orbit_invariant_v1.py`.)*

## 3. Three bridges from the lift geometry to the curve's own invariants
- **Pinned ↔ angle law [PROVED].** The angle-law pinned pair (area exactly `1/8=√3/16`) **=** the
  CM-stable (correction-free) wedges **=** the two sextants inside the μ₃-core `P∩ωP∩ω²P` (area 3/4).
  Exact polygon containment. *(`glv_pinned_wedge_containment_v1.py`, `_flap_pinned_sextant_v1.py`.)*
- **Correction ↔ norm-band law [VERIFIED].** The correction fires exactly on the high-norm shell:
  flap-rate `0` for `s<3/16` (inradius disk), `1` for `s>1/4` (short vertex), transition in between —
  the norm-band law's own breakpoints. *(`glv_correction_norm_v1.py`.)*
- **Pinned pair ↔ Frobenius angle [VERIFIED].** Pinned `= {1,4}` if `θ<30°` else `{0,3}`, with
  `θ = arg(π_p) mod 60° = atan2(f√3, t)` the **Sato–Tate Frobenius angle** (`4p=t²+3f²`) — read
  straight off the trace `t`. 0 violations / 69 primes, switch exactly 30°. secp `θ=50.55°→{0,3}`;
  the conjugate prime `π̄` (`60−θ=9.45°`) gives `{1,4}`, so the pinned pair **encodes which prime
  above p** (the sign of θ). *(`glv_pinned_satotate_v1.py`.)*

## 4. The family and the amicable geometry  **[VERIFIED]**
- **Seven-domain family.** `{π_p+u : u∈{0}∪μ₆}` — norms = `p` + the six sextic-twist orders (incl.
  `n=N(π_p−1)`, `n_t=N(π_p+1)`) — are concentric, θ-aligned, and **share one pinned pair**.
  *(`glv_seven_domain_map_v1.py`, `_amicable_twist_angle_v1.py`.)*
- **Amicable geometry.** The lift domain `P_p` and the scalar domain `P_n=(π_p−1)` overlap
  `1 − 4.1×10⁻³⁹`; their μ₃-cores satisfy `C_n ⊆ C_p` **exactly**; basis slippage is
  `R1_p−R1_n=(0,1)`, `R2_p−R2_n=(1,1)`. *(`glv_amicable_geometry_verify_v1.py`.)*

## 5. Inspection frontier — where the panels have been mapped so far
- **Fully mapped panel:** the lift cleanly linearizes the **multiplicative endomorphism** — the
  `{0,±R}` cocycle is exact and orbit-invariant. This is the coherent locus we understand.
- **Panels inspected, no seam surfaced (yet), controls valid:** the coordinate-level scalar readout
  — `v_n = eis_{π_n}(d)` vs `v_p = eis_{π_p}(x([d]G))` — showed no coupling at the readouts inspected
  (coarse 6-sextant; 16×16 and 64×64 lattice-cell grids; joint sextant–norm), across synthetic + 36k
  known-generator + real-82, with self-MI firing and decoy flooring (`MI ~ 1/N`). Likewise the
  group-law 3-point sum showed a spread additive correction. **Reading:** the *x*-coordinate is a
  faithful vehicle for the multiplicative structure but not for the additive/scalar structure, which
  lives in the nonlinear point map `x([d]G)`. That map is the next panel to inspect — not a closed
  one. *(`glv_amicable_bridge_probe_v1.py`, `_escalation_v1.py`, `_three_point_lift_v1.py`,
  `_doubling_scaling_v1.py`.)*

## 6. Open panels — the next inspections (invitations)
1. **Palelei frame operator on the lift (Int. 1).** Build the Gram/frame operator `C_T` on the
   Eisenstein lift split by μ₃-core (3/4) vs flaps (1/4); ask whether `λ_max/Tr` is governed by the
   flap fraction. Pure geometry we already hold exact — the most concrete next move.
2. **Rank-10 low-prime matrix under the μ₃-projection (Int. 2).** Does the exact rank-10
   orthogonality (Part VII) decompose into core-rotations + flap-reflections?
3. **Spectral dilution on the twist-order `−1`-branch primes (Int. 4).** Using the shared μ₃-geometry
   of the twists and `n_t = 3²·13²·3319·22639·C`.
4. **The nonlinear point map, joint-SET view.** The only structure that can survive the scramble is a
   joint property of the *set* the generator left — the finer/joint readouts of `x([d]G)`, not per-point.
5. **Is `ε` (the orbit label) an arithmetic object?** It is a geometric class function on the
   `(p−1)/6` μ₆-orbits; worth asking whether the rigid/broken partition has an independent
   description (a symbol, a norm condition) beyond "in core vs flap".
6. **Close the norm bridge to a θ-form.** The flap's internal split over sextants (~93% max pair, 0%
   pinned) is an exact rational per θ — write it as a closed form to complete the norm bridge.

## 7. The organizing lens + unchased directions (candidate seeds, not yet chased)
Recorded so future sessions can pick them up; all are **invitations**, tagged `[CANDIDATE]`.

**The lens (the generator behind all of these).** Every object across the curve work *and* the
`φ`-residue / Lonely-Runner preprints is **one arithmetic group `G` acting on a space**: the signal
lives in the `G`-covariant part, and the "defect" each proof exploits is where the `G`-orbits fail
to cover. `LRC φ(n)-law: G=(ℤ/n)*→` unclaimed slot `I₉`; `RH φ-residue: reduced residues →` off-line
zero (rank-1 concentration); `secp: G=μ₆=Aut(E) →` sought key structure; `functional eq: μ₂ →`
critical line. The shared spine is the **reduced-residue averaging operator over a ring** — the same
object as `P_n` (paper 4), the Ramanujan sum `c_n` (LRC φ(n)-law), and your `c_𝔫(β)` survival law —
read over `ℤ` vs `ℤ[ω]`. Its spectral ceiling is the large sieve; its survival core is `±1` (ℤ) / `μ₆` (ℤ[ω]).

**Curve-side operator seeds** (nearest to this programme; overlap §6's Int. 1/2/4):
- `[CANDIDATE]` **Eisenstein-φ frame operator** `S̃_{π_p}` on `(ℤ[ω]/π_p)^×`: does it act as identity on
  the non-trivial sector and propagate `μ₆`? Would give an operator-theoretic foundation for the GLV speedup.
- `[CANDIDATE]` **Rank-10 under μ₃-projection / ZFR forcing on `L(E,s)`**: apply the vertical-ZFR
  forcing+mesoscopic ceiling with the exact **rank-10** low-prime mode (not the preprint's rank-2) — does
  the CM structure modify the dispersion / bound the curve L-zeros?
- `[CANDIDATE]` **p-adic multiplicative domain** `D_{φ,p}`: `μ₆`-sparse formal group as the admissibility
  condition; the ASD/Honda bridge (`7ᵏC(3k,k)≡a_ℓ`) links archimedean `κ(L)` to the formal group ⇒ ask
  whether the critical line is enforced p-adically by `|Aut(E)|=6`. (= "survival core in 4 rings": ℤ, ℤ[ω], ℚ_p, L².)
- `[CANDIDATE]` **Spectral dilution on the twist-order `−1`-branch primes** (`n_t=3²·13²·3319·22639·C`):
  does `λ_max(C_T)/Tr(C_T)→0`, structurally constraining the twist's zeros / the order-169 subgroup?
- `[CANDIDATE]` **Amicability as a φ-residue fixed point**: evaluate `P_n` at `n=N(π_p−1)`; is the
  `p→n→p` 2-cycle (`Frob@n = 1−π`, `(1−π)−1=−π`) a fixed-point theorem for the multiplicative boundary,
  recasting Silverman–Stange amicability as a consequence rather than a coincidence?

**Cross-project bridges** (secp ↔ the RH / LRC preprints; heavier lifts):
- `[CANDIDATE]` **Finite-field zeta as an RH test-bench.** `L(T)=(1−πT)(1−π̄T)`, `|π|=√p` is a *theorem*
  and Euler-admissible — run the resonator/forcing against it; it either back-ports the correct forcing
  exponent or pinpoints the void step, against exact ground truth. (Pairs with the ASD/`O(√p)` "calibrated
  large-sieve constant".)
- `[CANDIDATE]` **Scaling-exponent referee.** Instrument the RH pooled energy `λ_max/Tr` and resonator
  energy with `power_scaling.py` (`z~√N` signal vs `~1/N` noise) — the *same* diagnostic as the BTC MI tests.
- `[CANDIDATE]` **LRC ↔ survival core (n mod 3).** The unclaimed slot `I₉ = μ₂={±1}` core = the ℤ-shadow of
  your `μ₆` core; the pairing type is set by `n` mod 3 — `n=7` gives `(ℤ/7)*=μ₆=Aut(E)` (the BS prime-filtering
  case), `n=11` only its `μ₂` shadow. Serves the LRC general-`n` "subsequent paper" (Remark 4.4) and cross-checks secp's `μ₆`.
- `[CANDIDATE]` **Shift/scalar-invariant core as the RH repair template.** Force the RH obstruction into a
  `γ`-invariant core (the analogue of LRC's cycle-index-free arithmetic / secp's `d`-invariant laws); a forcing
  that *can't* be made shift-invariant is itself the diagnosis of the flawed step.
- `[CANDIDATE, low-confidence]` **Curvature = Sato–Tate density.** Does the `C_T` eigenphase distribution match
  the angle law `p₀(θ)=(3/4)|cos2θ|/(2cos2θ+1)`? (Needs the eigenphase histogram computed.)

**Weaker rhymes (noted, not pursued):** three-distance / D-signature on the Farey–Stern-Brocot structure;
CM-invariant "runner configurations" (LRC on a μ₆-symmetric subtorus); the `1/8` coincidence (secp pinned
sextant vs `n=8` isolation radius) — numerology unless a defect geometry gives `√3/16`.

## Script index (all in `btc_puzzle_investigation/`, exact arithmetic)
`glv_fundamental_domain_law_v1.py` · `_geom_check_v1.py` · `_flap_pinned_sextant_v1.py` ·
`_pinned_wedge_containment_v1.py` · `_peer_zone_test_v1.py` · `_correction_norm_v1.py` ·
`_doubling_lift_v1.py` · `_doubling_scaling_v1.py` · `_amicable_twist_angle_v1.py` ·
`_three_point_lift_v1.py` · `_seven_domain_map_v1.py` · `_amicable_bridge_probe_v1.py` ·
`_amicable_bridge_escalation_v1.py` · `_amicable_geometry_verify_v1.py` · `_cm_orbit_invariant_v1.py` ·
`_pinned_satotate_v1.py`. Narrative: `glv_fundamental_domain_law_v1.md`.
