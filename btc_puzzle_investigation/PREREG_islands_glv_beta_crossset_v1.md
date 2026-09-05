# PRE-REGISTRATION — Dirichlet islands: GLV/μ₃ β-image cross-structure of the curve image

**Status: SPEC ONLY. FROZEN before any island/curve GLV data is seen. Decidable artifact.**
**Date 2026-07-21. Designed by the context-isolated `experiment-designer` agent; reviewed and persisted.**
Implementation target: `islands_glv_beta_crossset_v1.py`. Parent: `PREREG_islands_curveimage_jointset_v1.md`
(raw-coordinate additive/multiplicative energies + windowed metric already NULL, all controls firing,
executed N∈{64,128,252}, M=1024, B=999 — **not re-tested here**).

---

## 0. OBJECT + tautology check + baseline

- **Curve.** secp256k1 `E:y²=x³+7` over `p=2²⁵⁶−2³²−977`; prime order `N_ord`; generator `G`. Full-scale.
- **GLV.** `φ(x,y)=(βX,Y)`, `β=0x7ae9…01ee`, `β³≡1 (mod p)`, `β≠1`. On scalars `φ(P)=λ·P`, `λ³≡1 (mod
  N_ord)`, `λ` **full 256-bit**, fixed as the root with `x(λ·G)=β·x(G)` (other root = `β²`). μ₃ x-orbit of
  `X≠0` = `{X,βX,β²X}` (distinct) = x-coords of `{P,φP,φ²P}`.
- **Scalars.** `(n,k)=(2,1)`, `lo=2^{N−1}`, `base=3·2^{N−2}`, `S_islands={base±⌊lo/q⌋ : q≥2}∩[2^{N−1},2^N)`.
  `N≤255 ⇒` no wrap mod `N_ord`.
- **Object under test.** `𝒫={P_q=d_q·G=(X_q,Y_q)}`. Does `{⌊lo/q⌋}` induce GLV/μ₃ cross-structure in `𝒫`
  — exact φ-relations `X_i≡β^{±1}X_j`, or exact GLV-additive closure — absent from random band points?
- **TAUTOLOGY CHECK.** `X_i≡βX_j` ⇔ `d_i≡±λ^{±1}d_j (mod N_ord)`. Islands are **additive** in the
  reciprocal-floor lattice; `λ` is a **full-width multiplicative** cube root unrelated to that construction
  (`λd_j mod N_ord` ranges over all `[0,N_ord)`, not the ≤252-bit band). **No identity forces
  `base±⌊lo/q⌋≡λ(base±⌊lo/q'⌋)`** ⇒ **G1,G2 non-tautological.** The **additive** family
  `d_i±d_j±d_k≡0` (slopes, collinearity, group-additive energy, the `d⁺_q+d⁻_q=2base` anchor) IS the
  construction's own lattice = **S0 tautology ⇒ control only.**
- **Baseline.** All island x distinct (`X_i=X_j⇔d_i≡±d_j`, band-impossible). `X_i=βX_i⇔X_i=0` ⇒ G1 has no
  diagonal; any G1/G2 hit is a genuine off-diagonal GLV relation; Null-B expectation = point-mass ≈0.

---

## 1. STATISTICS — exact GLV cross-set definitions

**ADMISSION RULE (decidable).** A β-statistic `S` is ADMITTED as a leakage arm iff: **(A1)** `PC-φ` fires
`S`; **(A2)** `S` is exact-algebraic mod `p`/`N_ord`, not metric; **(A3)** its d-side reduction is not
forced by `S_islands`; **(A4)** `S` is **not value-equal, under `X↦βX`, to an already-null raw-X statistic**.
**Object-level fact:** the μ₃/GLV action is *multiplicative/projective* ⇒ **every exact GLV-orbit detector
is value-invariant under the global dilation `X↦βX`**; a literally non-invariant exact GLV statistic does
not exist (non-invariance needs an inhomogeneous reference — `Y`, a cube-character value, or the additive
lattice — all first-moment-floored / tautological / metric, §1a). So constraint-1 is read operatively as
*"invariant AND thereby a relabeling of an already-null raw-X statistic"*, and admission runs through
**A1∧A4**. Each kept statistic discloses its `X↦βX` value-invariance explicitly.

### G1 — exact pairwise GLV-orbit collision (PRIMARY)
`G1 := #{ ordered (i,j), i≠j : X_i≡βX_j (mod p) OR X_i≡β²X_j (mod p) }`.
- **compute.** `bx[j]=(β*X_j)%p`, `b2x[j]=(β*β%p*X_j)%p`; dict `X_i→i`; per `j` look up `bx[j],b2x[j]`,
  count `i≠j`. `O(M)`. Characterization: per hit record y-sign (`Y_i≡Y_j⇒+φ`; `≡−Y_j⇒−φ`) and `(q_i,q_j)`.
- **X↦βX.** `#{βX_i≡β·βX_j}=#{X_i≡βX_j}` ⇒ value-invariant (disclosed). **Admitted** via **A4** (Null-B law
  = point-mass at `≈2M²/p≈0`, categorically ≠ raw energy null `2M²−M` ⇒ not a relabeling) and **A1**
  (`PC-φ⇒G1=2c`). G1 is the detector the φ-pair plant exists to trip.
- **floor.** Exact incidence count (point-mass at 0); a single GLV pair is `O(1/√p)` in any first moment
  but `+2` to G1 ⇒ Weil/KS say nothing about it.

### G2 — exact three-island GLV-additive closure (SECONDARY)
`G2 := #{ (i,j,k) distinct : x(P_i⊕φP_j)≡X_k (mod p) }` ⇔ `d_i+λd_j≡±d_k (mod N_ord)`.
- **compute.** per `(i,j)`: `Q=P_i⊕φ(P_j)` via EC group law (`pow(z,p−2,p)`, batched); test `x(Q)∈dict`.
  `O(M²)` EC-adds.
- **X↦βX.** `x(φP_i⊕φ²P_j)=β·x(P_i⊕φP_j)`, `X_k↦βX_k` ⇒ value-invariant. **Admitted** via **A4**
  (null point-mass `≈2M³/p≈0`) and **A1** (`PC-G2` fires). G2 is the **`λ`-twist** of the tautological
  collinearity control (`λ=1` case, band-impossible=0): the `λ` makes it GLV-specific, non-tautological.
- **floor.** Exact incidence, point-mass at 0.

### 1a. DISCARDED (named)
- **`E_{×β}=#{X_i·βX_j≡X_k·βX_l}=#{X_iX_j≡X_kX_l}`** — β cancels ⇒ *literally* the null raw mult energy.
  **A4 fails.** DISCARD (canonical fake-β trap).
- **add/mult energy of `{βX_i}`** = raw energies (`79800=79800`). **A4 fails.** DISCARD.
- **`E_β=#{X_i−X_j≡β(X_k−X_l)}`, cross `#{X_i+βX_j≡X_k+βX_l}`** — value-invariant AND *diffuse*
  difference-set autocorrelations; a single φ-pair does not trip them ⇒ **A1 fails.** DISCARD → logged as
  **untested diffuse subspace** (§4); a G1/G2 null does not exclude it.
- **cubic-character balance `Σ(n_a−M/3)²`, cubic-ratio incidence** — first-moment / bilinear character sums
  at the Weil floor. DISCARD.
- **`Σχ(X_i)`, `Σψ(X_i)`** — first-moment, KS/Weil-floored. DISCARD.
- **windowed/NN βX proximity** — metric (prime fields ignore metric closeness). DISCARD.
- **slopes, collinearity, group-additive energy, `d⁺_q+d⁻_q=2base`** — additive scalar relations =
  construction lattice (band-impossible, provably 0). **A3 tautological.** Kept as CONTROL only.

---

## 2. ARMS & CONTROLS (matched on `M`, band `[2^{N−1},2^N)`)

- **TEST `S_islands`** — deterministic enumeration; image `{d_q·G}`.
- **NULL-B** — `M` uniform scalars in band, `random.Random(20260721)`, same map, `B=999`. Reference null.
- **STRUCTURED-INERT AP** — `d_j=start+j·step` (span-matched); GLV-inert. Islands fire ∧ AP inert ⇒
  islands-specific.
- **PC-φ (PRIMARY plant, G1, VOID gate).** `(M−2c)` islands ∪ `c` φ-pairs `{d_a·G,(λd_a)·G}`, `c∈{1,2}` ⇒
  `x(2nd)=β·x(1st)` ⇒ `G1=2c` deterministically.
- **PC-φ² (direction, G1).** `{d_a·G,(λ²d_a)·G}` ⇒ trips β² term.
- **PC-G2 (plant, G2, VOID gate).** random ∪ one triple `{d_i·G,d_j·G,((d_i+λd_j)%N_ord)·G}` ⇒ `G2≥1`.
- **C-add (control).** `#{d_i+d_j≡±d_k}` provably 0 on islands ⇒ any firing is multiplicative-`λ`, not additive.

**Disclosed power limit.** Plants inject *exact* GLV relations (only cheap route without ECDLP search);
diffuse β-difference coupling (`E_β`) has no cheap plant ⇒ left untested, disclosed (§4).

---

## 3. POWER

- **G1.** Null-B `E[G1]≈2M(M−1)/p≈2⁻²³⁵` ⇒ point-mass at 0; `P(any of 999 nulls ≥1)≈0`. Smallest detectable
  = **1 exact GLV-orbit pair**; observed `G1≥1⇒p_MC=1/(B+1)`, true p `≈2⁻²³⁵`; power≈1. `PC-φ⇒G1=2`.
- **G2.** Null-B `E[G2]≈2M³/p≈2⁻²²⁵` ⇒ point-mass at 0. Smallest detectable = **1 GLV-additive triple**;
  power≈1; `PC-G2⇒G2≥1`.
- **Bonferroni:** `{G1,G2}×{64,128,252}=6` cells ⇒ `α*=0.05/6=0.00833`; `B=999⇒`min p`=0.001<α*`. PRIMARY =
  **G1 @ N=128,M=1024** (single). Any true hit has p≈2⁻²²⁵ ⇒ multiplicity immaterial.

---

## 4. SCOPE & PARAMETERS

- Curve secp256k1 full-scale; `(n,k)=(2,1)`. `N`: primary **128**, secondary **{64,252}**. `M`: primary
  **1024**, secondary **4096** (`B=199`, G1). **G2 at M=1024** (`O(M²)`; fallback M=512, null unchanged),
  `B_G2=199`. Fixed: `(n,k),G,β,λ,seed=20260721`, plant `d_a`, island rule.
- **μ₃ config count:** `μ₆=μ₃×{±1 on y}`, `±1` fixes x ⇒ **3 x-configs** `{X,βX,β²X}`, not 6; identity
  excluded.
- **Untested (null scoped to G1,G2 ONLY):** (i) diffuse β-difference coupling `E_β`; (ii) `≥4`-island GLV
  relations; (iii) cubic-character μ₃-phase (floored); (iv) GLV couplings using `Y` jointly with `X`;
  (v) 2-adic/formal-group filtration. Not excluded by a G1/G2 null.

---

## 5. EXACTNESS

All signal-path `int`: scalars; `β,λ,βX,β²X,λd` mod `p`/`N_ord`; EC law via `pow(z,p−2,p)`; coords mod `p`;
collisions via `dict`/`set`; counts. `base=3·2^{N−2}`, `⌊lo/q⌋` via `//`. **No `/`, `float`, `**0.5`,
`math.*`, `round` on any key/coord/feature.** p-values exact rationals. `λ` selected by exact test
`x(λ·G)==(β·x(G))%p`. `check_no_float.sh` must pass. No carve-out.

---

## 6. DECISION RULE + PRE-COMMITTED OUTCOME TABLE

**Rule** (per `S∈{G1,G2}`, arm `A∈{islands,AP}`): `p_MC=(1+#{b:S(NullB_b)≥S(A)})/(B+1)`;
**FIRES ⟺ p_MC≤α*=0.00833.** VOID gate: `PC-φ` must fire G1, `PC-G2` must fire G2, else halt (no verdict).

| Arm / statistic | Outcome | Pre-committed conclusion |
|---|---|---|
| **G1 islands (PRIMARY)** | FIRES `G1≥1`, AP inert, PC-φ/φ² fired | Island x-set contains **exact GLV-orbit pair(s)** `X_i≡β^{±1}X_j` ⇒ `P_i=±φ^{±1}(P_j)`, `d_i≡±λ^{±1}d_j`. Islands-specific. Magnitude `G1`; power≈1; scope N=128,M=1024,B=999. NEXT PROBE: list `(q_i,q_j)`+y-sign, test vs `v_q≈lo/q`; report symmetry type. Do NOT verdict. |
| **G1 islands** | FIRES islands AND AP | GLV pairs generic to structured interval d-sets, not islands-specific. Bounded magnitude, NOT leakage. |
| **G1 islands** | NULL `=0`, PC-φ/φ² fired | SCOPED bound: no exact GLV pair among `M` islands; smallest detectable=1 pair, power≈1; scope N∈{64,128,252},M∈{1024,4096}. NOT "no GLV structure" — diffuse `E_β`, ≥4-body, cubic-phase, Y-couplings untested (§4). |
| **G1 islands** | NULL, PC-φ did NOT fire | VOID: control failed; debug detector. |
| **G2 islands** | FIRES `G2≥1`, AP inert, PC-G2 fired | 3-body GLV-additive closure `d_i+λd_j≡±d_k`. Characterize indices, next probe. |
| **G2 islands** | NULL `=0`, PC-G2 fired | SCOPED bound (3-body GLV-additive), as G1-null. |
| **C-add (control)** | provably 0 on islands | Confirms any firing is multiplicative-`λ`, not additive. No leakage info. |

---

## 7. FALSIFICATION

- **GLV STRUCTURE PRESENT ⇔** G1 @ N=128,M=1024 FIRES (`G1≥1`, p_MC≤0.00833) AND G1(AP) inert AND PC-φ/φ²
  fired.
- **GLV-GENERIC AT TESTED POWER ⇔** `G1=0` and `G2=0` across N∈{64,128,252} while PC-φ,PC-φ²,PC-G2 fired;
  reported as a scoped bound (smallest detectable = 1 GLV pair / 1 triple; §4 untested list; phrase
  *"generic in exact GLV-orbit and GLV-additive collision functionals of the curve image at this power"*) —
  never "no signal / closed."
- **VOID ⇔** any planted positive fails to fire.

---

**Load-bearing for implementation.** (1) G1/G2 nulls are **point-masses at ≈0** ⇒ exact-collision detectors,
power≈1 for ONE relation, **blind to diffuse coupling** (`E_β` untested; a null does not exclude it).
(2) **Every exact GLV detector is value-invariant under `X↦βX`** (μ₃ action multiplicative/projective);
G1,G2 are admitted via A1∧A4 (fire on φ-pair plant; null ≠ raw energies), the fake-β energies (`E_{×β}`,
energy-of-`{βX}`) are discarded by name. (3) `λ` (multiplicative, full-width) is unrelated to the additive
reciprocal lattice ⇒ G1/G2 non-tautological; the additive `d_i±d_j±d_k≡0` family is the construction's own
lattice (band-impossible) ⇒ control only.
