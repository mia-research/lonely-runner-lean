# PRE-REGISTRATION — Dirichlet reciprocal-floor islands: curve-image JOINT-SET structure

**Status: SPEC ONLY. Written and FROZEN before any island / curve data is seen. Decidable artifact.**
**Date 2026-07-21. Designed by the context-isolated `experiment-designer` agent (object-level, no outcome predicted); reviewed and persisted verbatim.**
Implementation target: `islands_curveimage_jointset_v1.py`. Parent context: `RESULT_nkd_dterms_subsurface_v2.md`
(the T=1 islands = Dirichlet reciprocal-floor lattice, d-side, exact).

---

## 0. OBJECT (name the object, not a proxy)

- **Curve.** Real secp256k1: `E: y² = x³ + 7` over `p = 2²⁵⁶ − 2³² − 977`; prime group order `N_ord`
  (cofactor 1); standard generator `G`. This IS the full-scale object — there is **no** `p≈10⁵`→`2²⁵⁶`
  scale gap; the scope caveat is about the *statistic family and island subset*, not curve size.
- **Scalar (island) construction.** Fixed Farey label **`(n,k)=(2,1)`** ⇒ `lo=2^{N−1}`,
  `base = 2^{N−1}+⌊lo·1/2⌋ = 3·2^{N−2}`. Island scalar set
  `S_islands = { base ± ⌊lo/q⌋ : q=2,3,4,… } ∩ [2^{N−1}, 2^N)`.
  (`q=1` out of band; `q≥2` ⇒ `⌊lo/q⌋≤2^{N−2}` ⇒ both `±` in band. `N≤255` ⇒ every island `<2^{255}<N_ord`
  ⇒ **no scalar wraps mod N_ord** — deliberate artifact avoidance.)
- **Curve image (object under test).** The point SET `𝒫 = { P_q = d_q·G = (X_q,Y_q) : d_q ∈ S_islands }`.
- **Property under test.** Does `𝒫` carry **non-generic JOINT (multi-point) coordinate structure**
  absent from a matched set of points from random band-scalars?
- **Tautology check (mandatory).** Features read the **field-coordinate map** `x(·),y(·)` — NOT part of
  the island (scalar-reciprocal) construction ⇒ feature and target disjointly constructed ⇒ **not a
  tautology** ⇒ test valid before it runs. The one tautological quantity (`S0`, group-law energy) is a
  **control only** — it measures the scalars' own additive lattice `{d_q}`, computable without the curve.
- **Provable no-collision baseline.** For distinct islands `X_i=X_j ⟺ d_i≡±d_j mod N_ord`; `d_i=d_j`
  excluded; `d_i+d_j≈3·2^{N−1}<N_ord` for `N≤254` ⇒ impossible. Hence **all island x-coords distinct**;
  any off-diagonal collision is a genuine relation, not a `±P` artifact.

---

## 1. STATISTICS — exact joint definitions + why each evades the single-point Weil/KS floor

Point set `{(X_i,Y_i)}_{i=1}^M`, integers mod `p`.

**Why the floor does not reach these.** Weil (single character) and Kohel–Shparlinski
(`max_t|Σ_i ψ_t(X_i)|≤4√p+1`, uniform) bound the **first moment** — a *linear* functional. Every
statistic below is a **fourth moment** (energy) or a *quadratic windowed* functional. With
`Ŝ(t)=Σ_i e_p(tX_i)`, additive energy `=(1/p)Σ_t|Ŝ(t)|⁴`; the KS first-moment bound gives only
`E ≤ M⁴/p + 16pM`, vs random baseline `≈2M²` — structure can live in `[2M²,16pM]` undetected by KS.
The pre-registered null is empirical (Null-B), so validity does not depend on this; the ceiling only
certifies "not already floored."

- **S1 — additive energy of x (PRIMARY).** `E⁺ₓ := #{(i,j,k,l): X_i+X_j≡X_k+X_l (mod p)} = Σ_s r(s)²`,
  `r(s)=#{(i,j):(X_i+X_j) mod p = s}`. Integer. Detects **exact additive relations** (Sidon defect).
- **S2 — multiplicative energy of x.** `E×ₓ := #{(i,j,k,l): X_i·X_j≡X_k·X_l} = Σ_m t(m)²` over `X_i≠0`.
  Exact. Detects **exact multiplicative relations**.
- **S3 — additive energy of y.** S1 on `{Y_i}`. Independent coordinate.
- **S4 — windowed pair-difference concentration of x (the GRADED arm).** `Δ:=⌈p/M⌉`.
  `N_Δ := #{(i,j): i≠j, ((X_i−X_j) mod p)<Δ or >p−Δ}`. Integer. Detects **approximate** clustering the
  exact energies (point-mass) are blind to. Null ≈ Poisson mean `2M(M−1)Δ/p ≈ 2M`, sd `≈√(2M)`.
- **S0 — group additive energy (CONTROL ONLY, tautological).** `A_grp := #{(i,j,k,l): P_i⊕P_j=P_k⊕P_l}`
  `= Σ_R g(R)²`. Equals additive energy of the **scalar** multiset `{d_q} mod N_ord` (computable without
  the curve). Proves the tuple-collision machinery works on real EC points. **A firing is NEVER leakage.**

### 1a. DISCARDED (each secretly single-point or tautological)
- `Σ_i ψ(X_i)`, `Σ_i χ(X_i)`, single-coordinate marginals / gaps / nearest-neighbour — first-moment ⇒
  KS-floored. FORBIDDEN.
- Coarse/**binned** additive energy of one coordinate — its informative part = single-point discrepancy
  (KS-floored). Only the **exact** (`T=p`) energy is kept.
- Slopes `λ_ij=(Y_i−Y_j)/(X_i−X_j)`, collinearity `P_i⊕P_j⊕P_k=O`, `x(P_i±P_j)` collisions — all reduce
  to **scalar** relations `d_i±d_j±…≡0` = the S0 tautology. DISCARDED as leakage arms; kept only in S0.

---

## 2. ARMS & CONTROLS — matched on cardinality `M` and band `[2^{N−1},2^N)`

- **TEST — `S_islands`.** Enumerate `q=2,3,4,…`; append `base+⌊lo/q⌋` then `base−⌊lo/q⌋` if in-band and
  new; stop at `M` distinct. Deterministic (no post-hoc subset).
- **NULL-B (matched null; user-required).** `M` scalars uniform in `[2^{N−1},2^N)`,
  `random.Random(seed=20260721)`, same `d·G` map. `B=999` resamples. PRESERVES band, `M`, the map, the
  valid-x value set. DESTROYS island structure. **Reference null; all p-values are ranks vs this.**
- **STRUCTURED-INERT NULL — AP scalars.** `d_j=start+j·step`, `start=min(S_islands)`,
  `step=⌊(max−min)/(M−1)⌋`. PRESERVES a structured interval-spread d-set (max additive scalar structure);
  DESTROYS reciprocal spacing. If S1 fires on islands AND AP ⇒ "any structured d-set," not islands.
  (AP also fires S0 ⇒ doubles as point-machinery positive.)

**PLANTED-POSITIVES (must fire or the arm's null is VOID).**
- **PC-1 (machinery, S0).** Islands & AP fire S0; Null-B does not. Confirms tuple-collision on EC points.
- **PC-2 (end-to-end, S1/S2/S4 — PRIMARY plant).** `(M−2c)` random curve points ∪ `c` pairs
  `{d_a·G,(N_ord−d_a)·G}` (shared x ⇒ ≈4M off-diagonal additive quads/pair). `c∈{1,2,4}`. Islands
  provably contain no such `±` pair ⇒ the plant's structure is genuinely absent from the test arm.
- **PC-3 (S1/S3 detection, residue-only).** Residue AP `{(1+2j) mod p}`; energy `(2/3)M³`. Dilution
  `f∈{2/M,4/M,8/M,16/M,64/M,256/M,1}` → smallest detectable additive-quadruple count.
- **PC-4 (S2 detection, residue-only).** Residue GP `{3^j mod p}`; mult energy `(2/3)M³`.

**Disclosed power limit.** No cheap curve-point set with planted *distinct-x* additive energy exists
(needs ECDLP-flavoured search). PC-2 plants duplicated-x end-to-end; PC-3/4 plant distinct-value quads on
residues; S0 calibrates the tuple machinery. This bounds the design's power and is disclosed, not hidden.

---

## 3. POWER — planted calibration + smallest detectable effect

- **S1,S2,S3 — near-deterministic point mass at `2M²−M`** (accidental `M⁴/p≈2⁻²¹²`). **Exact-collision
  detectors:** power ≈1 to detect **≥1** off-diagonal exact relation at `B≥300`; **blind to approximate**.
  Smallest detectable = **one exact quadruple**. PC-3 confirms detection down to `fM≈2–3` injected quads.
- **S4 — graded**, Poisson mean `≈2M`, sd `≈√(2M)`. Detectable excess `≳z·√(2M)`: at `M=1024`, `≳136`
  extra sub-`Δ` ordered pairs (planted cluster of `c` near-coincident x's gives `c(c−1)` ⇒ `c≳12`); at
  `M=4096`, `≳272` (`c≳17`).
- **PC-2** injects `≈4Mc` off-diagonal quads ⇒ fires S1/S2 at `p=1/(B+1)` for `c=1`.
- **Bonferroni family (counted now):** significance tested on **islands** for `{S1,S2,S3,S4}×{N=64,128,252}
  = 12` cells ⇒ `α*=0.05/12=0.004167`. `B=999` ⇒ min achievable `p=0.001<α*` ✓. **PRIMARY headline =
  S1 @ N=128, M=1024** (single; the rest are pre-committed secondary characterization, NOT a max-over-cells).
  AP-arm & Null-B-arm p-values are interpretive (qualify the islands result), not extra islands tests.

---

## 4. SCOPE & PARAMETERS

- **Curve:** real secp256k1, full-scale — no scale-banner discount.
- **Farey label:** `(n,k)=(2,1)` fixed (`base=3·2^{N−2}`).
- **`N`:** primary **128**; secondary **{64, 252}** (all `≤255` ⇒ wrap-free). Coords full 256-bit mod `p`.
- **`M`:** primary **1024**; secondary **4096** (`B=199`) for S4 power.
- **`B`:** 999 (primary), 199 (`M=4096`).
- **Fixed:** `(n,k)`, curve, `G`, `seed=20260721`, plant const `d_a`, `Δ=⌈p/M⌉`, island rule.
- **Varies:** `N`, `M`, arm.
- **Symmetry-config counts (no invariance is *claimed*):** island `±` = ℤ/2 ⇒ 2 configs; `Aut(E)` reaches
  `x` via `μ₃` ⇒ **3** distinct x-configs per orbit (**not 6**: `μ₆=μ₃×{±1 on y}`, `±1` fixes `x`).
  Islands are not `×β`-closed ⇒ **any S2 firing must be checked for β-related x's before naming μ₃.**
- **Untested joint functionals (null is scoped to S1–S4 ONLY, never "the set is generic"):** (i) GLV/μ₃
  eigen-coordinate `βX`; (ii) rational coords (`y/x` …); (iii) `≥3`-point group invariants beyond additive
  energy; (iv) 2-adic / formal-group filtration; (v) any statistic coupling `X`&`Y` jointly (S1–S4 treat
  them separately). Structure in these is **not excluded** by a null here.
- **Compute:** primary ≈ `1003` point-sets × (`M` scalar-mults + energies `O(M²)` + window) — bounded.

---

## 5. EXACTNESS (int-only signal path)

Every signal-path quantity is Python `int`: scalars; EC group law via `pow(z,p−2,p)`; coords `mod p`;
energies (integer counts); products/sums `mod p`; windows; `base=3·2^{N−2}`, `⌊lo/q⌋` via `//`. **No `/`,
`float`, `**0.5`, `math.*`, `round` on any key/coord/feature.** p-values exact rationals `#{·}/(B+1)`.
`check_no_float.sh` must pass before the run. No float carve-out needed.

---

## 6. DECISION RULE + PRE-COMMITTED OUTCOME TABLE

**Rule** (per statistic `S`, arm `A∈{islands,AP}`): `S(A)` exact int; `p_MC=(1+#{b:S(NullB_b)≥S(A)})/(B+1)`
(one-sided upper). **FIRES ⟺ `p_MC≤α*=0.004167`.** VOID gate: any designated PC does not fire ⇒ that
statistic's null is uninformative — halt, no verdict.

| Arm / statistic | Outcome | Pre-committed conclusion |
|---|---|---|
| **S1 islands (PRIMARY)** | FIRES `E⁺ₓ>2M²−M` AND S1(AP) inert | Islands' x-set carries EXACT additive relations absent from random AND AP ⇒ islands-specific non-generic joint structure. Scope N=128,M=1024,B=999. NEXT PROBE: extract firing quadruples, list `q`-indices, test vs `v_q≈lo/q`; report symmetry type, do NOT verdict. |
| **S1 islands** | FIRES on islands AND AP | Excess is generic to structured interval d-sets, not islands-specific. Reclassify as bounded magnitude, NOT islands leakage. |
| **S1 islands** | NULL `=2M²−M`, PC-2/3 fired | SCOPED bound: no exact x-additive relation; smallest detectable = 1 quadruple, power≈1, scope N∈{64,128,252},M∈{1024,4096}. NOT "no structure" — approximate coupling (S4) & untested functionals (§4) not excluded. |
| **S1 islands** | NULL, PC-2/3 did NOT fire | VOID: positive control failed; null uninformative. Debug. |
| **S2 islands** | FIRES islands, not AP | Islands-specific exact MULTIPLICATIVE x-relation. Verify firing quads not β-related x's (§4) before naming μ₃/GLV. Characterize, next probe. |
| **S2 islands** | NULL, PC-4 fired | Scoped bound (multiplicative), as S1-null. |
| **S3 islands** | FIRES / NULL (PC-3 fired) | y-coordinate template: firing ⇒ islands-specific y-additive relation + next probe; null ⇒ scoped bound. |
| **S4 islands** | FIRES `N_Δ` excess `≥z·√(2M)`, not AP | Islands' x show APPROXIMATE clustering beyond Poisson & AP. Magnitude `N_Δ`, power (`c≳12` @M=1024), scope. Next probe: locate clustered `q`-indices. |
| **S4 islands** | NULL, PC-2 fired | Scoped bound: x-diff Poisson-consistent ±z√(2M); no clustering ≳`c≈12`(M=1024)/`17`(M=4096). Not "no structure." |
| **S0 (control)** | fires islands+AP, not Null-B | Machinery live (tautological group energy). Carries NO leakage info. |
| **S0** | does NOT fire on islands/AP | VOID: detection machinery broken; whole run uninformative. Fix & re-run. |

---

## 7. FALSIFICATION (single conditions, before the run)

- **NON-GENERIC (hypothesis retained) ⇔** PRIMARY cell **S1 @ N=128,M=1024 FIRES** (`E⁺ₓ>2M²−M`,
  `p_MC≤0.004167`) **AND S1(AP) does not fire**. (S2/S3/S4 sharpen but the single primary is S1-∧-AP-inert.)
- **GENERIC AT TESTED POWER (hypothesis abandoned at this scope) ⇔** S1,S2,S3 at baseline `2M²−M`
  (`p_MC=1`) AND S4 within `±z√(2M)` while every PC fired. Reported as a **scoped bound** carrying the
  smallest detectable effect (1 exact quad; `c≈12` cluster) + the §4 untested-functional list + the phrase
  *"generic in additive/multiplicative/near-collision functionals of raw affine coords at this power"* —
  **never** "no signal / avenue dead / closed."
- **VOID (no verdict) ⇔** any positive control fails, or S0 fails on islands/AP.

---

**Two load-bearing facts for implementation:** (1) at `p=2²⁵⁶` the S1/S2/S3 null is a **point mass** at
`2M²−M` ⇒ exact-collision detectors (blind to approximate — do not read an S1 null as "smooth structure
excluded"; S4 is the only graded arm). (2) `S0` and any slope/collinearity statistic are **tautological**
(= scalar additive energy) ⇒ controls only; a firing there is not leakage.
