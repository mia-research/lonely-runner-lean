# PREREG — weight-1 PHASE ramp on the μ₆-broken public lift (Brick C, ROADMAP_REDIRECT_v3)

**Status: FROZEN. No data seen. `experiment-designer` pre-registration.**
Date: 2026-08-21. Scope banner: model scale (p ≤ ~10³); a positive licenses NO 2²⁵⁶ claim.
Predecessors read for grounding: `ROADMAP_REDIRECT_v3.md` (Brick C), `POSITIVE_FINDINGS_MASTER_v12.md`
rows M14/M15/M16/M28/P4/P10/P13/P16/P18/N1/N9/N14, `RESULT_weight1_proved_v1.md`,
`RESULT_arm2_eigenvalue_v1.md`, `RESULT_n1_120deg_exact_v1.md`, `int1_frame_operator_v1.py`,
`ANALYSIS_public_gate_glv_carry_circularity_v1.md`.

**No leakage / key-recovery / ECDLP claim is asserted by this registration.** The pre-committed
expectation (see §3, §7, §9) is a BOUNDED NULL. A positive would be extraordinary and is gated
behind every control below plus OOS replication.

---

## 0. OBJECT PINNING — what is on-disk, what is a proxy, what is NOT covered  *(mandatory disclosure)*

The Brick-C object as literally stated — "per-point PHASE `Φ(d)` on the 2-dim weight-1 Frobenius
eigenspace of `A_new`" — **cannot be pinned to a single on-disk construction**, for a reason that is
itself part of the finding:

- The A_new weight-1 eigenspace (dim-4 `H¹`, even char poly `T⁴+mpT²+p²`, `m=1`, eigenvalues `±60°/±120°`,
  2+2 split by `[−1]/μ₄`; `RESULT_arm2_eigenvalue_v1.md`, `RESULT_weight1_proved_v1.md`) is a
  **frequency-domain / cohomological** object. Its natural per-point access is the character-sum family
  `V(a)=Σ_P χ₂(y_P)e_n(a·d)` / `U(a,b,c)` — which is a SUM over all `d` and contains the target
  frequency `e_n(a·d)`. There is no on-disk public map "single point `P_d` ↦ vector in `H¹(A_new)`"
  that is (i) public, (ii) per-point, and (iii) linear so an oblique projector can act on it. (Such a
  map would be the cover route `φ:E→A_new` of Brick E followed by `A_new`-dlog — a DIFFERENT object,
  and it collapses to the orbit label / DLP; `N14`, `ANALYSIS_public_gate…`.)
- The only public per-point lift on disk is `eis(x)` (`int1_frame_operator_v1.py`): exact rationals
  `(u,v)`, with `eis(βx)=ω·eis(x)` reduced. It is a lift of the **x-coordinate** into `ℤ[ω]`, NOT of
  `A_new`'s `H¹`, and it is **x-only ⇒ `[−1]`-invariant** (M14: x-only readouts are even in `d`). An
  oblique projector built on `eis` alone therefore CANNOT break the `[−1]/μ₄` symmetry that M16's
  forced-null rests on. To break `[−1]` the readout MUST use `y`.

**Registered proxy (the smallest decidable version).** A **public, per-point, μ₆-symmetry-BROKEN
PHASE readout** built from the two on-disk public ingredients — `eis(x)` (the μ₃ axis) and `χ₂(y)`
(the `[−1]` / sextic-twist ℤ/2 axis, P10) — with an oblique diagonal projector `M` over the
`μ₆ = μ₃ × ⟨[−1]⟩` isotypes computed from the PUBLIC ℤ/3×ℤ/2 character table (no `d`, no `T`).

**What this proxy COVERS:** whether a public per-point phase that (a) uses both coordinates, (b) is
genuinely `μ₆`-broken (admissibility-gated, §1c), carries **d-linear** information (alignment to
`a·d mod n`) beyond the μ₆-orbit label, against a phase-shuffle null that preserves magnitude —
i.e. exactly the axis M14's forced-magnitude theorem left open.
**What it DOES NOT COVER:** the true frequency-domain `A_new` Frobenius eigenspace. The identification
"`eis`-lift μ₆-isotype (j=1,s=1) ↔ `A_new` weight-1 cohomological subspace" is **UNPROVEN** (`N9`:
the module `W` is unidentified; `N1` open). A null here bounds THIS public per-point phase channel with
power+scope; it does not bound the frequency-domain `V(a)`/`U` phase, which is separately governed by
M14/M16. This coverage gap is a first-class output of the run, not a footnote.

---

## 1. OBJECT (the concrete decidable construction)

Curve `E: y²=x³+7` over `F_p`, `p≡1 mod 3`, `n=#E(F_p)` prime; `d ↔ [d]G=(x_d,y_d)` the DLP bijection
`ℤ/n ↔ E(F_p)`. All ingredients below are computable from the PUBLIC point `(x_d,y_d)` and public
constants (`β`, reduced basis `R1,R2`, the ℤ/3×ℤ/2 character table). `d` NEVER enters the `Φ` path
arithmetically (construction audit, §DC).

**(a) Per-point seed functional (isotype-MIXING, by design).**
For a point `Q=(x,y)`, let `(u,v)=eis(x)` (exact rationals, `int1_frame_operator_v1.build(p)`), and
`χ₂(y)=y^{(p−1)/2} mod p ∈ {+1,−1}`. Freeze
```
φ₀(Q) := u(eis(x))  +  i · χ₂(y) · v(eis(x))       (i = Gaussian unit; u,v exact)
```
`φ₀` is NOT μ₆-equivariant: under `φ:(x↦βx)`, `(u,v)↦R_{120°}(u,v)` so `u` carries BOTH conjugate
μ₃-lines (j=1 and j=2), and `χ₂(y)` toggles the `s` (=[−1]) axis. This multi-isotype support is what
makes the oblique `M` non-vacuous (§1c). *(Freeze note: `φ₀` chosen before data; any change post-run
voids the spec.)*

**(b) μ₆-isotype amplitudes via the PUBLIC orbit.** The full μ₆ orbit of `P_d` is publicly computable
(`φ^m: x↦β^m x`; `[−1]^t: y↦(−y)`). Define, over the group `μ₃×⟨[−1]⟩ ≅ ℤ/3×ℤ/2`,
```
A_{j,s}(P) := Σ_{m=0}^{2} Σ_{t=0}^{1}  ζ₃^{-jm} · (−1)^{-st} · φ₀( φ^m [−1]^t P ),   j∈{0,1,2}, s∈{0,1}
```
(`ζ₃=e^{2πi/3}`). These are the point's per-isotype amplitudes.

**(c) OBLIQUE projector `M` (breaks μ₆ — the pivotal object).** Frozen diagonal weights over isotypes:
```
w_{1,1} = 1        (the weight-1, [−1]-ODD isotype: χ(φ)=ζ₃, χ([−1])=−1 — the μ₃-weight-1 / odd-in-d
                    half the master localizes xy to; the "one weight-1 2-dim eigenspace" analogue)
w_{0,0} = w_{0,1} = 0        (kill the μ₃-TRIVIAL isotypes — "down-weight the null eigenspace")
w_{2,0} = w_{1,0} = w_{2,1} = 1/4     (partial, UNEQUAL ⇒ oblique/non-unitary ⇒ μ₆ BROKEN)
```
`M` is computed only from the public ℤ/3×ℤ/2 character table (P10). Readout:
```
Φ(d) := arg( Σ_{j,s} w_{j,s} · A_{j,s}(P_d) )   ∈ (−π, π]
```

**(d) Target (disjoint from Φ).** The d-LINEAR functional `τ_a(d) := a·d mod n`, tested via its phase
`2π·a·d/n`. Built from `d`; shares no sub-construction with `Φ` (which is built from `P_d`'s public
coordinates via `eis`/`χ₂`). We test `Φ` vs `τ_a`, NEVER a residual `r=v−w` against `w`
(`feedback_residue_vs_component_tautology`).

---

## 2. STATISTIC (exactly one, named now, with its null distribution)

Per prime, the aimed phase-lock coefficient at the FROZEN primary frequency `a*=1`:
```
R_p(a) := (1/(n−1)) Σ_{d=1}^{n−1} exp( i·( Φ(d) − 2π·a·d/n ) ),    S_p := |R_p(1)| ∈ [0,1]
```
`S_p` is a PURE PHASE statistic (lift magnitudes are discarded by `arg`); the Fourier coefficient of
`exp(iΦ)` at the target frequency — AIMED at the predicted d-linear ramp, POOLED over all `d`
(not a max-over-cells). Per-prime exact permutation p-value `P_perm(p)` (integer count, §3).

**THE SINGLE PRE-COMMITTED DECISION STATISTIC** over the frozen primary ladder `𝒫`:
```
X := −2 Σ_{p∈𝒫} ln P_perm(p)     (Fisher combination)    ~   χ²_{2|𝒫|}  under the null.
```
Distribution under the null: each `P_perm(p)` is Uniform(0,1) by construction (exact permutation),
so `X ~ χ²_{2|𝒫|}`. One statistic, one null law. `a*=1` frozen; all other `a` are EXPLORATORY (§SUB).

**Immunity to M14 (checked, not assumed).** M14's forced quantity is the l²-energy `Σ_{b,c}|U|²=p²(n−1)`.
`S_p` depends only on the phases `Φ(d)`; the null (§3) preserves the entire magnitude profile. No
l²-normalized fidelity enters. The forced-magnitude control is NOT used as the null (M14: it validates
nothing).

---

## 3. MATCHED CONTROL (the null — must preserve everything except the tested alignment)

**PRIMARY null (d-label permutation).** Draw a uniform random bijection `π` on `{1,…,n−1}`; recompute
`S_p^π := |(1/(n−1)) Σ_d exp(i(Φ(π(d)) − 2π d/n))|`. This **preserves** the full multiset `{Φ(d)}`,
every lift magnitude, and the μ₆-orbit structure of `Φ` (a symmetry the readout has by construction);
it **destroys only** the specific `Φ↔(a*·d)` alignment. `P_perm(p) = (1 + #{b: S_p^{π_b} ≥ S_p}) / (B+1)`,
`B=2000` frozen, seeds `0…1999` (integer-seeded; the ranking needs no float threshold).

Why this null is valid here and is NOT the M16-invalid shuffle: M16's invalid null destroys a
symmetry the readout has *by definition*. Here `Φ` is deliberately μ₆-BROKEN (admissibility-gated
below), so there is no μ₆-covariance for a shuffle to invalidly break; and the permutation preserves
`Φ`'s own distribution. The tested structure (alignment to the linear ramp) is exactly what the
permutation breaks — the correct matched null.

**SECONDARY null (isotype-phase randomization, confirmatory).** Randomize `arg A_{j,s}` iid per point
while preserving `|A_{j,s}|`, recompute `Φ`, then `S_p`. Preserves the energy/magnitude profile of the
eigenspace (the task's "phase-random WITHIN the eigenspace"); destroys phase alignment. Must agree with
the primary null in verdict; a disagreement is a disclosed deviation, not a result.

**(c) ADMISSIBILITY GATE — `M` must genuinely break μ₆ (run BEFORE §2; a fail is INADMISSIBLE, not a null).**
The pivotal M16 check. For a frozen random sample of `μ₆`-orbits, measure the circular variance of
`Φ` around each orbit AFTER removing the covariant orbit-label ramp (the rigid +60° arithmetic
progression that a μ₆-COVARIANT `M` would force):
```
G := mean_orbits CircVar( { Φ(g·P) − ℓ(g) } over g∈μ₆ ),   ℓ = the covariant label ramp.
```
- **Gate PASS iff `G ≥ G_min` (frozen `G_min = 0.05` rad²).** Firing check on the gate itself: a
  deliberately μ₆-COVARIANT `M` (equal weights `w_{j,s}=1 ∀`) must return `G ≈ 0` (FAIL); the chosen
  oblique `M` (§1c) must return `G ≥ G_min` (PASS). If the oblique `M` fails the gate, `Φ` is constant
  on μ₆-orbits ⇒ the d-aligned test is FORCED-null ⇒ **the run is INADMISSIBLE (wrong object), reported
  as such, NOT as a bound.**

---

## 4. PLANTED CONTROL (positive — must fire, else null is uninformative)

- **Hard plant.** Inject `Φ*(d) := 2π·a*·d/n` (a genuine d-linear ramp) in place of `Φ`. Require
  `S_p → 1` and `P_perm(p) ≤ 1/(B+1)` at every prime. If it does not fire, the pipeline is broken → VOID.
- **Graded plant (POWER).** `Φ_ε(d) := arg( (1−ε)·e^{iΦ_rand(d)} + ε·e^{i·2π a* d/n} )`, `Φ_rand` iid
  uniform. Report `ε_min(p)` = smallest `ε` at which `S_p` exceeds the null 95th pct with prob ≥ 0.80
  (250 trials/ε; ε-grid `0.02·k`). This is the detectable ramp amplitude (§5).
- **Hard NULL (false-positive calibration).** A phase-random readout (`Φ_rand` iid uniform, and,
  separately, `Φ` = a public function of `P` with no d-linear content: `Φ_noise(d)=arg φ₀(P_d)` with
  equal-weight `M`) must NOT fire: empirical FP-rate of `X` at `α=0.01` must be `≤ 2α` over the ladder.

---

## 5. POWER (computed now, per prime)

Under the null, `Re R_p, Im R_p` are averages of `n−1` unit vectors with null-random phase, so
`E_null|R_p|² ≈ 1/(n−1)` and `(n−1)|R_p|² ≈ Exp(1)`. A ramp of amplitude `ε` gives `E|R_p| ≈ ε`.
Detection floor (95th pct of null, power 0.8): `ε_min(p) ≈ (z_{.95}+z_{.8})/√(n−1) ≈ 2.6/√(n−1)`.

| prime | `n≈` | `ε_min` (single prime) |
|---|---|---|
| p=163 (≡7 mod12, secp class) | ~163 | ~0.20 |
| p=349 (≡1 mod12) | ~349 | ~0.14 |
| OOS S-stratum p~800–2500 | ~10³ | ~0.06–0.09 |

Fisher combination over `|𝒫|` primes lowers the *joint* detectable `ε` by ≈`√|𝒫|`. **Zero power at
2²⁵⁶** (banner). A bound reported without `ε_min(p)` attached is not a result.

---

## 6. SCOPE (every number inherits this)

- Primary ladder `𝒫`: `p=163` (≡7 mod 12, secp's own class), `p=349` (≡1 mod 12), roadmap-named.
- OOS ladder (drawn by point-counting BEFORE the first `Φ`, frozen with a SHA-256 as in
  `RESULT_n1_120deg_exact_v1.md`): smallest `p>547, p≡7 mod12, #E prime` (stratum S, secp class) and
  smallest `p>547, p≡1 mod12, #E prime` (stratum C). Selection rule frozen; the actual primes are NOT
  chosen after looking at `Φ`.
- Full-group enumeration (`d=1…n−1`, `d=0=O` excluded — the unique μ₆-fixed point, M15). Both `p mod 12`
  strata required (secp is `p≡7 mod12`). No subset of `d` is filtered after the fact.
- Every reported number carries `(p, n, ladder-membership)`. Model scale only.

---

## 7. FALSIFICATION (written before the run)

- **Kills "weight-1 phase leaks d" (a NULL, not a closure):** admissibility gate PASSES (`M` breaks μ₆),
  hard+graded plants fire, hard-null calibrated (FP ≤ 2α), and `X` does NOT exceed `χ²_{2|𝒫|}` at α=0.01
  on the primary ladder. Report: "the (j=1,s=1)-isotype public per-point phase carries no d-linear
  alignment at `a*=1` above `ε_min(p)` [table], scope §6" — a **bounded phase channel with power+scope**,
  NOT "no structure" and NOT a closure of the frequency-domain A_new phase (§0 coverage gap).
- **Makes the run INADMISSIBLE (no verdict either way):** admissibility gate FAILS (`M` did not break
  μ₆ ⇒ forced-null); OR any plant fails to fire; OR hard-null FP-rate > 2α (miscalibrated). Report the
  failed gate; do not report a bound.
- **A POSITIVE requires ALL of:** gate PASS + hard/graded plants fire + hard-null calibrated + `X`
  significant on the FULL primary ladder + OOS ladder replicates (p<0.01 each) + explicit distinctness
  from M28 (§DIST). Absent OOS replication it is "unreplicated candidate," never a leak.

---

## 8. EXACTNESS (int/Fraction signal path; float carve-out named)

- **Exact (no float):** point arithmetic `[d]G` and the μ₆ orbit (`β^m x mod p`, `−y mod p`); `eis`
  coordinates `(u,v)` (exact `Fraction`/`rdiv` per `int1_frame_operator_v1`); `χ₂(y)=y^{(p−1)/2} mod p`;
  the permutation-null ranking (integer counts, integer seeds).
- **Float carve-out (analytic size only, NO key in path):** `ζ₃, ω, i, exp/arg` enter ONLY in the
  isotype DFT `A_{j,s}`, the phase `Φ`, and the statistic `S_p`/`X` — all downstream of, and never
  feeding back into, any key/point/target arithmetic. `d` is never in the `Φ` path. This matches the
  folder rule: a float transform is allowed as a monotone statistic ranked against a matched
  permutation null.
- `check_no_float.sh` (AST grep) must PASS on the signal-path files (point/eis/χ₂ code) before any `S_p`
  is computed. If it fails, VOID.

## DC. Construction audit (disjointness / anti-tautology)
`Φ` path: `P_d=(x_d,y_d) → eis(x_d),χ₂(y_d) → φ₀ → A_{j,s} → M → arg`. The scalar `d` appears ONLY as
the DLP index selecting `P_d`; it is never an arithmetic input to `Φ`. Target path: `d → a·d mod n`.
Disjoint. No residual `r=v−w` is regressed on `w`. The permutation null WOULD expose a tautology (if
`Φ` were built from `d` directly, permuting d-labels would break it and read null) — here it reads the
genuine alignment question.

## DIST. Distinctness from M28 (must be stated with any positive)
M28 = `3·argT(a₀,b) ↔ χ₂(b)`: **b-indexed** (field-frequency domain), `a₀` generic, PROVED to NOT leak
the scalar `d`. This experiment is **d-indexed** (per scalar point), eigenspace-restricted, aimed at
`a·d`. It uses no `b`-sweep and no `T`. A positive here is a NEW d-leaking phase channel, categorically
distinct from M28; a positive that reduces on inspection to a `b`-phase (i.e. `S_p` null but a
b-correlation fires) is NOT this channel and is reported as such.

## SUB. If the effect lives in a subspace we are not projecting onto  *(mandatory)*
A null on `S_p(k*=(1,1), a*=1)` bounds ONLY that projection. Registered EXPLORATORY (FWER-controlled,
Holm over the family; never promoted, never used to override the pre-commit): the other weight-1
isotype `(2,1)`; frequencies `a*∈{2, 3, λ mod n, λ² mod n}` (the GLV-image ramps). If the primary is
null but an exploratory cell fires and REPLICATES OOS, that becomes the object of a NEW prereg — it
does not retro-fit this one.

---

## 9. PRE-COMMITMENT TABLE (filled before the run)

| gate → plant → hard-null → primary `X` (α=0.01, full ladder) → OOS | CONCLUSION (frozen) |
|---|---|
| Gate FAIL (`G<G_min`) | **INADMISSIBLE** — `M` did not break μ₆; forced-null; report failed gate, no bound. Fix `φ₀`/`M` under a NEW prereg. |
| Gate PASS, any plant fails to fire OR FP-rate>2α | **VOID** — pipeline broken / null uninformative; report and fix. |
| Gate PASS, plants fire, hard-null clean, `X` NOT significant | **BOUNDED NULL** (the expected outcome per the redundancy barrier §0): "(j=1,s=1) public per-point phase carries no d-linear alignment above `ε_min(p)` [§5 table], scope §6." A brick that bounds the weight-1 PHASE channel with power+scope. NOT a closure; NOT a bound on the frequency-domain A_new phase (§0). |
| Gate PASS, plants fire, hard-null clean, `X` significant, OOS FAILS to replicate | **UNREPLICATED CANDIDATE** — not a leak; log for a fresh-prime prereg. |
| Gate PASS, plants fire, hard-null clean, `X` significant, OOS REPLICATES, distinct from M28 | **EXTRAORDINARY POSITIVE** — the first PHASE separation of character from random on the weight-1 axis (what M14's forced-magnitude theorem left open). Characterize (which isotype, which `a`, `ε` achieved); attach the §0 coverage gap and the scale banner; NO 2²⁵⁶ claim; open the identification-to-A_new question (N9) as the immediate follow-up. |

**Either admissible outcome is a brick:** a phase concentration above the phase-random floor is a
d-leaking phase channel to characterize; a null is the weight-1 phase channel bounded with power+scope —
the honest residue M14/M16 left open, distinct from the frequency-domain object they govern.

*Frozen parameters (changing any voids the spec): `φ₀`, `M` weights, `a*=1`, `𝒫={163,349}`, OOS
selection rule, `B=2000`, `α=0.01`, `G_min=0.05`, graded-plant grid/trials, isotype `k*=(1,1)`.*
