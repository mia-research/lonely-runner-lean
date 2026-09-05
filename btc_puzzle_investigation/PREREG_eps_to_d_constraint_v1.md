# PRE-REGISTRATION — Does public `eps(X)` supply the d-containing LBE carry (and reduce the d2 search)?

**Status: PRE-REGISTERED. Written before any run. No data seen.**
Scope object: curve `E: y^2 = x^3 + 7` (j-invariant 0, Aut = μ6, GLV endomorphism φ, A=0).
Feature source: `int1_frame_operator_v1.py::build(p)` → `eps(X)`, and `s = enorm(eis(X))/p ∈ [0,3/4]`.
Target source: ARSENAL tool 7 carry `ε = [r1+r2 ≥ n]`, `r_i = d_i·λ^j`; single-key carry
`c = ((-1)^s d0 λ^j - d)/n`; congruence `d ≡ d0(-1)^j - ⌊d0 λ^j/n⌋ (mod 3)`.

The two coupled questions:
- **(1) IDENTITY** — is `eps(X)` (function of x ALONE, no d in path) a deterministic function of the
  d-side carry `ε` / `c`?
- **(2) PAYOFF** — in the two-key setting (known d1, unknown d2), does PUBLIC `eps`/`s` cut the d2
  search space *beyond* the baseline that uses all public data except `eps`?

---

## DECIDABILITY VERDICT (read first — the question's circularity is handled, not ignored)

- **Part (1) is decidable, non-circularly**, by *exact enumeration on a small prime-order curve*:
  `eps` is built from x alone (its path contains no d — verified from `build(p)`); `ε`/`c` are built
  from the scalars alone. The two constructions are **disjoint**, so this is NOT the residue-vs-
  component tautology (`r=v−w` vs `w`). The remaining tautology risk is the **μ3-orbit forcing** of
  `eps`; it is neutralized by (a) counting only ONE representative per ⟨φ⟩-orbit and (b) a matched
  control that permutes *within* the forced symmetry (see §3). This is the only design that a true
  UNFORCED identity survives while a symmetry-forced coincidence does not.

- **Part (2) is NOT independently decidable. It is a COROLLARY of (1).** The circular trap: "does
  `eps` constrain d2?" measured by computing `eps(x([d2]G))` over candidate d2 is circular — it needs
  `[d2]G`, i.e. the search itself. The non-circular form: `eps` is read **once** from the PUBLIC sum
  point `P_sum=(d1+d2)G`; the constraint on d2 flows through the carry congruence using ONLY that one
  public `ε`-value + public j + known d1, with **no group multiplication of a candidate**. This is
  legitimate **iff `eps(public x)=ε` is an established identity, i.e. iff (1) fires on unforced reps.**
  **Minimal change that makes (2) self-standing:** define baseline candidate set
  `B = {d2' : consistent with all public non-eps constraints}` and augmented
  `B' = {d2' ∈ B : predicted_ε(d2') = observed eps(x(P_sum))}`, where `predicted_ε` is computed from
  the **carry/interval formula** (tool 4/5), never from `[d2']G`. Payoff = `log2(|B|/|B'|)` bits.
  If the (1) identity is null, `B'=B` and the measured payoff is exactly 0 — a clean null, not a
  circular artifact.

---

## 1. OBJECT

- **Feature (public, no d in path):** `eps(x) ∈ {0,1,2}` and `s(x)=Fraction(enorm(eis(x)), p) ∈ [0,3/4]`,
  both exact integer/Fraction functions of the x-coordinate. Confirmed from `build(p)`: `eis`, `om2`,
  the R1/R2 comparisons — no scalar d anywhere in the path.
- **Target (d-side, disjoint construction):** two-key carry bit `ε(d1,d2,j) = [d1 λ^j + d2 λ^j ≥ n]`
  (primary); single-key `c(d) mod 3` and `[c≠0]` (mechanism/secondary). Built from scalars only.
- **Tautology check:** feature and target share NO construction step. They share only the point/scalar
  bijection (x ↔ d on ⟨G⟩) and the μ3 symmetry — the first is neutralized by measuring a *predictive
  map* not mutual information (determinacy is void, see §5), the second by §3's within-symmetry control.

## 2. STATISTIC (exactly one)

**Primary:** `M` = number of ⟨φ⟩-orbit representatives r (out of `U` unforced reps) for which the
**pre-registered, frozen** map `φ_map(eps(x(P_sum,r)))` equals the disjointly computed `ε(d1,d2_r,j_r)`.

- Frozen map (NOT fitted post hoc): `φ_map(eps) = [eps ≥ 1]` (0→0, 1→1, 2→1); target `ε ∈ {0,1}`.
- Sampling: enumerate `d2` over ⟨G⟩ with d1 fixed; keep exactly ONE representative per ⟨φ⟩-orbit of
  `P_sum=(d1+d2)G` (this is the "count only unforced" step — μ3-forced agreement is removed by
  construction). `U` = number of distinct orbits.
- Readout: `z = (M − μ_null)/σ_null` with `μ_null,σ_null` from §3's matched control; and the EXACT
  permutation p-value `p = (#{control M ≥ real M} + 1)/(B+1)`. No float decides the verdict.

**Secondary (mechanism, pre-registered but not primary):** single-key `M_c` on frozen map
`eps ↦ (eps mod 3)` vs `c mod 3`; and the directional gate `M_gate`: does `s < 3/16 ⇒ ε=0` hold
(count reps with s<3/16 and check ε; a single violation falsifies the *sufficiency* direction).

Statistic is pooled/targeted (a single match count on frozen maps), not a max-over-cells.

## 3. MATCHED CONTROL

Null must reproduce every structure the real pairing has EXCEPT the tested `eps↔ε` link.

- **Control permutation:** re-pair `eps(x(P_sum,r))` with `ε(d1, d2', j_r)` where `d2'` is drawn
  uniformly from the SAME ⟨φ⟩-orbit-class / same `j`-bin as the true `d2_r` (preserve j, s, orbit
  position — everything the μ3/μ6 symmetry forces), randomizing only the fine within-class alignment.
- **Preserves:** μ3-orbit forcing of `eps`, the j distribution, the s-branch structure, the marginal
  of `ε`. **Destroys:** the specific point-to-carry correspondence.
- **Why this control and not a plain shuffle:** a plain shuffle also breaks a genuine μ3-forced
  coincidence, reproducing the z=+5000 phantom. Here: a REAL unforced identity → `M_real ≫ M_control`;
  a μ3-forced tautology → agreement preserved in BOTH → `M_real ≈ M_control` → correctly no signal.
- `B ≥ 2000` control draws for the permutation p-value.

## 4. PLANTED CONTROL (must fire before any verdict)

- **Positive plant:** define `eps_plant(x(P_sum,r)) := ε(d1,d2_r,j_r)` (carry injected as the feature),
  run the FULL pipeline. Required: `M_plant = U` and `z_plant ≥ 6` with `M_real` replaced by plant.
  If the positive plant does NOT fire, the null is uninformative — **STOP, fix pipeline.**
- **Negative plant:** `eps_plant := ` a μ3-symmetry-respecting random field independent of `ε`.
  Required: `M ≈ M_control`, `z ≈ 0`. Confirms no false-positive channel.
- **Gate plant:** force `ε=0` whenever `s<3/16` and random elsewhere; `M_gate` must report 0 violations
  in the plant. Confirms the directional test can detect a true gate.

## 5. POWER

- `H(d|x)=0` (bijection) framing is **void** — determinacy is not structure. Power is stated on the
  PREDICTIVE statistic `M`, not on any mutual information.
- Under matched null, per-rep chance match prob `q` (largest cell of `φ_map(eps)` vs `ε`; expect
  q≈0.5–0.7). `M ~ Binomial(U,q)`. Full identity ⇒ `M=U`, giving
  `z ≈ sqrt(U·(1−q)/q)`. Worked: U=100, q=0.6 ⇒ z≈8.2; detectable (z≥6) for **U ≥ ~55** at q=0.6.
- **Partial/gate identity** covering unforced fraction f: extra matches ≈ `f·U·(1−q)`; detect when
  this exceeds `3σ = 3·sqrt(U q(1−q))`. Compute the exact number for each curve's U at run time and
  report it; a bound with no U-power number is not a result.
- **Curve selection for power:** prime-order curves with U≥60. Start `p=43` (m=31, matches
  OPEN_d2_congruence, λ=5, β=6) as the wired sanity curve; add prime-order `y^2=x^3+7` curves found by
  search with m up to a few thousand so `U=m/3 ≳ 300`. Report `U` and the achievable z on every curve.
- **Real-82 arm has ZERO power for the carry identity** and this is pre-registered: ARSENAL records the
  82 solved keys all give `c=0, j=0, s=0` (each key is its own orbit-min) ⇒ `c`/`ε` have **no variance**
  on that sample ⇒ the identity statistic is undefined/powerless there. The 82 are reported as a
  consistency spot-check ONLY (does `eps` land where `c=0` predicts), never as a test with a verdict.
  The powered real-analog is the constructed known-generator set with LARGER d2 (not orbit-min), where
  `c` varies. This mirrors the "N=82, f=1.0-needed, zero-power null" failure and refuses to repeat it.

## 6. SCOPE

- Curve `y^2=x^3+7` over `F_p`, `p ≡ 1 (mod 12)` (μ3 and χ2 defined, GLV φ exists), with **prime group
  order m**. Named testbed: `p=43` (m=31). Additional prime-order curves by search, each reported with
  its `(p, m, λ, β, U, achievable z)`.
- `λ, β` = the CM endomorphism eigenvalue / field cube-root used by `build(p)`; `n=m` the group order.
- Two-key: d1 fixed (choose 3 distinct d1 values, report each separately — never pooled without scope);
  d2 enumerated over ⟨G⟩.
- **Both sets:** (a) small enumerable curves = the decidable core; (b) constructed known-generator set
  (MT19937 through the same select-bitlen→curve pipeline) with varied d2 = the powered analog; (c) real
  82 solved keys = zero-power consistency spot-check only (§5).
- **Every number produced inherits `(curve p, m, d1, U)` and may never be stated without it.**

## 7. FALSIFICATION

- **Full identity H_A falsified** if, on a curve with U giving achievable z≥6, `M_real` lies inside the
  matched-control distribution (`p_perm > 0.05`, i.e. `M_real ≤ control 95th pct`) AND the positive
  plant fired. Written before the run.
- Falsification of the FULL identity does **NOT** license "no structure." On H_A falsification the run
  MUST test the residual subspace: the directional gate `s<3/16 ⇒ ε=0` (`M_gate`), and the single-key
  `eps mod 3 ↔ c mod 3` (`M_c`). Structure may live in the gate region / a mod-3 subclass even if the
  full binary identity is null.
- **Scoped null recorded ONLY if** H_A, the gate, AND `M_c` all fail against the matched control with
  U-power z≥6, plant fired. Phrasing bound to method+curve-list+U+plant, per conditional-negatives rule.
  A magnitude/bound is never written as "no structure."

## 8. EXACTNESS

- Signal path is int/Fraction throughout: `eps` integer (from `build`), `eis`/`om2`/R1/R2 integer,
  `enorm` integer, `s=Fraction(enorm, p)`, `c`/`ε` integer, carry `⌊d0 λ^j/n⌋` integer floor. Curve
  arithmetic (`padd`,`mul`,`find_point`) is exact modular int from `hybrid_char_sum_v1.py`.
- Comparisons `s < 3/16` done as integer cross-product `16·enorm(eis(x)) < 3·p`, never float.
- **No float in the signal path.** The Int.1 `aniso`/`moments` float code is NOT invoked here. No FFT.
  No float carve-out is claimed or needed.
- `check_no_float.sh` must pass on the run script before it executes.

## 9. PRE-COMMITMENT (filled BEFORE the run)

| Outcome | Conclusion (pre-committed) |
|---|---|
| Positive plant does NOT fire | Null uninformative. STOP. Fix pipeline. No verdict on the question. |
| Plant fires; `M_real ≫ control` (z≥6), on unforced reps | IDENTITY (1) holds on scope. Proceed to PAYOFF (2): compute `log2(|B|/|B'|)` bits saved on d2 vs the eps-free baseline; report bits with `(curve,m,d1,U)`. Grade EMPIRICAL/VERIFIED-scope, tag the exact curves. |
| Plant fires; `M_real ≈ control` (p>0.05); gate `M_gate` fires (0 violations, gate-plant confirmed) | Full identity null; PARTIAL payoff via the gate: `ε=0` pinned for the s<3/16 fraction. Report that fraction and the resulting d2-interval cut, scoped. |
| Plant fires; full identity, gate, and `M_c` all null at z≥6 | SCOPED null: "`eps`/`s` do not supply `ε`/`c` via the pre-registered maps on curves {list}, U-power z≥{value}, plant fired." Conditional phrasing. NOT "eps is featureless." |
| `M_real ≫ control` but only on forced reps / control also high | Tautology flagged (μ3-forcing). No identity claim. Report the forcing, not a signal. |
| Any statistic/map/curve/d1 changed after seeing data | Deviation. Disclose in an audit note; the changed result is EXPLORATORY, not the pre-registered verdict. |

**Nothing about the likely outcome is asserted here. The spec fixes the maps, control, plant, power
threshold, and scope before the run; the run fills the numbers.**
