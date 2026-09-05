# PRE-REGISTRATION v2 (HARDENED) — c=±b diagonal PHASE probe + correct-shape re-test of the −13.99σ deficit

**Status: authoritative pre-registration (experiment-designer, isolated pass).** Hardens the
`[PROVISIONAL]` draft `PREREG_cbpm_phase_deficit_v1.md`. The draft's self-audit flagged three
UNCOVERED frame layers — **matched-control adequacy, object/disjointness, scope/falsification**. This
version resolves all three at the object level (derivations below), so they are no longer provisional;
where a residual judgment remains it is named. Reuses v1's two probes and the T1b.0 result
(`RESULT_t1b0_tail_exponent_v1.md`: real |U| marginal is sub-Rayleigh, k≈1.4, calibrated k_random≈1.9–2.0).

Object: `U(a,b,c) = Σ_{d=1..n−1} e_p(b·x_d + c·y_d)·e_n(a·d)` on `E: y²=x³+7`, prime-order ⟨G⟩ of order
`n=m`, `e_p(t)=exp(2πi t/p)`, `e_n(t)=exp(2πi t/n)`. `x_d,y_d` = coords of `[d]G`. Symmetries (exact):
`U(−a,b,c)=U(a,b,−c)` (x even, y odd in d) and `U(a,b,c)=U(aλ,bβ,c)` (GLV μ3, y fixed).

---

## 0. FORCED vs FREE — the disjointness ledger (gate-free, run FIRST; derivations to VERIFY exactly)

The FREE/FORCED lever (M14/N7/M15) says any L²-normalized magnitude/fidelity is forced-equal
real-vs-random. Making this precise decides which statistics are admissible:

- **FORCED (excluded as statistics):**
  - `Σ_a |U(a,b,c)|² = n(n−1)` per (b,c) — Parseval; holds for ANY unit-modulus phase sequence
    (including every surrogate below). ⇒ any L²-fidelity `⟨target,U⟩/(‖target‖‖U‖)` is forced-equal.
  - **`Σ_a (Im U)²` is FORCED — NEW, corrects the draft's "Im isotype = distinct free object".**
    Derivation to verify exactly: `Σ_a U(a,b,c)² = n·Σ_d φ_d φ_{−d}` with `φ_d=e_p(bx_d+cy_d)`; since
    `x_{−d}=x_d, y_{−d}=−y_d`, `φ_d φ_{−d}=e_p(2b·x_d)` ⇒ `Σ_a U(a,b,c)² = n·Σ_d e_p(2b x_d)` — REAL,
    c-independent, x-only. Hence `Σ_a(Im U)² = (n(n−1) − n·Re Σ_d e_p(2b x_d))/2` is a function of the
    x-marginal alone. **⇒ ΣIm² is EXCLUDED.** The free Im-content is the small-ball/tail of the Im
    values, not their 2nd moment.
- **FREE (admissible):**
  - **Phases** `arg U(a,b,c)` — not determined by the forced 2nd moment. In particular the
    interaction phase `Φ` (§T1a) is orthogonal to `Σ|U|²`.
  - **Magnitude-distribution SHAPE beyond the 2nd moment** — the k≈1.4 small-ball exponent is free
    (that is why T1b.0 could measure it); the harmonic mean (tail-weighted) is free.

**0-deliverable:** exact-integer verification of `Σ_a U(a,b,c)² = n·Σ_d e_p(2b x_d)` and
`Σ_a|U|²=n(n−1)` on the scan curves; the admissible-statistic list is frozen by the result. No matched
null, no gate — pure structural computation.

---

## PROBE T1a — c=±b diagonal as a PHASE test on the free subspace

### 1. STATISTIC (exactly one)

**Interaction phase** (magnitude-free, marginal-free by construction — the mixed 2nd difference over
the corners {(b,0),(0,b),(b,b),(0,0)} of the (b,c) square, on the c=+b diagonal):
`Φ(a,b) = arg U(a,b,b) − arg U(a,b,0) − arg U(a,0,b) + π`  (the +π absorbs `arg U(a,0,0)=arg(−1)`).
If arg U were additively separable in the b- and c-contributions, `Φ≡0`; `Φ` isolates the
NON-SEPARABLE (interference) phase and is identically 0 on either marginal.

**Primary scalar:** the pooled mean-resultant length on unforced reps within each c₂ stratum:
`R_S = | (1/M_S) Σ_{(a,b)∈ reps, a>0, a∈S} exp(i·Φ(a,b)) |`, one value per stratum
`S ∈ {cubic-residue, cubic-non-residue}` of a (n≡1 mod 3, verified). Under the null R_S≈1/√M_S;
non-separable coherence ⇒ R_S ≫ that. **Verdict = integer permutation p-value**
`p_S = (#{R_S^surrogate ≥ R_S^real}+1)/(B+1)`, B≥2000. Report per stratum; NEVER pool the two strata
(the c₂ branch law grades them differently: residue root-orders [1,1,2,2] vs non-residue [3,3,6,6]).

**Count only UNFORCED:** the only symmetry acting within {c=±b} is `U(−a,b,b)=U(a,b,−b)` (a↔−a couples
+b- and −b-diagonals). Quotient it: use `a>0` representatives on the +b diagonal only; the −b diagonal
at −a is then determined and excluded. GLV maps b→bβ off the diagonal, so it does not act within-slice
and forces nothing here.

### 2. MATCHED CONTROL — GLOBAL-REPARTITION (the frame layer that produced the false +10.36)

**Why not per-block:** the +10.36 artifact came from an analytic per-block null treating correlated
`(a₀,c)` blocks as independent (~2.85× variance under-count). The null here recomputes the ENTIRE Φ
field and R_S from ONE global surrogate, so all inter-(a,b) correlation is carried intrinsically — no
independence assumption anywhere.

**The impossibility that dictates the construction (stated so it is not glossed):** on a real curve
`x_d,y_d` are locked to the same d, so NO permutation preserves both coordinate marginals while breaking
only their coupling. The adequate null therefore re-pairs the y-multiset onto the x-orbits **while
preserving the forced symmetry**:
- Index the `(n−1)/2` sign-orbits `{d,n−d}` (x constant, y sign-flipped on each).
- Draw a global random bijection π on these orbits; assign to x-orbit i the `|y|`-value of orbit π(i),
  keeping `y_{n−d}=−y_d`. Recompute the full U(a,b,c) tensor, Φ, and R_S from this surrogate.
- **Preserves:** x-marginal exactly; y-marginal `|y|`-multiset and the odd-in-d sign structure (so the
  y-marginal magnitude law and the `U(−a)=U(a,·,−c)` symmetry hold); `Σ|U|²=n(n−1)` (Parseval,
  automatic); the sub-Rayleigh magnitude shape (same |y| multiset). **Destroys:** which x-orbit each y
  attaches to = the x–y interaction = exactly what Φ measures.
- A true non-separable alignment survives (R_real ≫ surrogate); a coincidence forced by the preserved
  symmetries is reproduced in every surrogate (R_real ≈ surrogate) → no false positive.

**MANDATORY flat-Z-across-N diagnostic (hard gate, not advisory).** Compute
`Z_S(N) = (R_S^real − mean_surrogate)/sd_surrogate` at two rep-counts N and ≥10N (vary the b-set size,
e.g. |b|=4 vs ≥40, and/or a-subsample). A genuine effect has R_S = O(1) effect size ⇒ `Z ∝ √N` ⇒
`Z(10N)/Z(N) ≈ 3.16`. **If the ratio is < 1.5 (flat Z), DECLARE variance miscalibration and STOP — do
not report Z.** (With the recompute-from-surrogate null the empirical variance is correct by
construction; flat-Z is the confirmation that it is, and a tripwire if the chosen b-values are
themselves correlated.)

### 3. PLANTS (must fire before any verdict)

- **Positive:** inject a true coupling `φ_d := e_p(bx_d + cy_d + κ·x_d y_d mod p)` (κ fixed) ⇒ R_S ≫
  surrogate, and `Z ∝ √N` (NOT flat). If it does not fire, null uninformative — STOP.
- **Negative:** a separable field `φ_d := e_p(bx_d)·e_p(cy_d)` reordered so Φ≡const ⇒ R_S ≈ surrogate,
  Z≈0, flat. Confirms no false-positive channel.

### 4. POWER (per curve; M_S = unforced reps per stratum)

Under the null R_S≈Rayleigh(scale 1/√(2M_S)); a population phase-concentration ρ is detectable at
z≈3 when `ρ ≳ 3/√M_S`. `M_S ≈ (n−1)/2 · |b-set| / 2`. With |b-set|=20:

| role | p | n | M_S ≈ | detectable ρ (z≈3) |
|---|---|---|---|---|
| scan | 547 | 547 | 2730 | 0.057 |
| scan | 907 | 967 | 4830 | 0.043 |
| confirm | 1303 | 1249 | 6240 | 0.038 |
| confirm | 1831 | 1753 | 8760 | 0.032 |
| confirm | 2143 | 2089 | 10440 | 0.029 |

Report M_S and detectable ρ actually achieved per curve; a bound with no M is not a result.

---

## PROBE T1b.1 — re-score the −13.99σ deficit against the CORRECT-SHAPE null

### 1. STATISTIC (exactly one)

`D_stat = HM_real − HM_ref`, where `HM = harmonic mean over a≠0 of |U(a,b,c)|/√n` (tail-weighted; free
per §0). The −13.99σ deficit is `D_stat < 0` (real harmonic mean below reference). Pooled over the same
(b,c) set as T1b.0 {x-axis, y-axis, c=±b diagonal, generic}; also reported split by c₂ stratum.

### 2. MATCHED CONTROL — correct sub-Rayleigh symmetry-type, global-repartition

The concern: the deficit was scored against a **Rayleigh (k=2)** null, but the real marginal is
sub-Rayleigh (k≈1.4). Note the DIRECTION: smaller k ⇒ more small-|U| mass ⇒ larger `⟨1/|U|⟩` ⇒ **lower**
harmonic mean — i.e. sub-Rayleigh alone predicts a deficit. So the null MUST share the k≈1.4 shape.

- **Primary null (correct-shape):** the two-complex-eigenvalue form the sub-Rayleigh exponent implies
  (A_new a 2-D CM abelian surface; `V(a)=2i√p(sinθ₁+sinθ₂)`). Draw the whole `{θ₁(a),θ₂(a)}` field
  globally i.i.d. uniform, build the surrogate U of matched scale, recompute `D_stat`. This reproduces
  k≈1.4 by construction; a deficit that survives it is BEYOND the marginal shape. Global-repartition
  (one field → whole statistic); B≥2000; verdict = integer permutation p-value.
- **Reported context nulls (same D_stat, not the verdict):** (i) Rayleigh (k=2) — reproduces the old
  −13.99σ; (ii) value-multiset permutation — the null it already survived. Reporting all three isolates
  which null the deficit lives beyond.
- **Flat-Z-across-N diagnostic:** same mandatory gate as T1a (vary the (b,c) count 10×; require Z∝√N).

**Object/disjointness note:** `D_stat` is tail-driven hence free (§0); it is NOT an L²-fidelity and NOT
ΣIm² (which §0 shows is forced/excluded).

### 3. PLANTS

- **Positive:** deplete small |U| on a thin a-set by a fixed factor (a real beyond-shape deficit) ⇒
  `D_stat` significant vs the two-phase null. Must fire.
- **Negative (crucial):** a PURE two-phase target (k≈1.4, no extra depletion) ⇒ `D_stat ≈ 0` vs the
  two-phase null (z≈0) EVEN THOUGH it shows a large false deficit vs the Rayleigh null. This
  demonstrates the correct-shape null absorbs the marginal and only a beyond-shape deficit fires. Must
  NOT fire vs two-phase; SHOULD fire vs Rayleigh (confirming Rayleigh was the wrong null).

### 4. POWER

Per curve, N_a = n−1 magnitudes × |(b,c) set|. HM sampling sd ≈ shape-dependent; detectable relative
deficit at z≈3 ≈ `3·sd(HM)/HM ≈ 3/√(N_eff)` with N_eff the effective independent count. Report N_eff
and the detectable relative deficit per curve; the historical effect is ~0.06–0.10%, so the run must
show N_eff large enough to resolve <0.1% (N_eff ≳ 10⁶) or state the arm is under-powered rather than
read a null as absence.

---

## SCOPE (frozen OOS, p≡7 mod 12 = secp class, for the c₂ grading)

- **SCAN:** p=547 (n=547), p=907 (n=967). All development + first pass here only.
- **CONFIRM (frozen now, computed prime-order p≡7 mod 12):** p=1303 (n=1249), p=1831 (n=1753),
  p=2143 (n=2089). A scan hit must survive its primary null on ALL THREE under a fresh confirmatory
  prereg. No statistic/null/stratum/(b,c)-set/curve may change after the scan.
- Every number inherits `(p, n, stratum, (b,c)-set, M_S/N_eff)`.

## EXACTNESS

Integer signal path: `x_d,y_d,d,a,b,c` and the args `(b x_d + c y_d) mod p`, `a d mod n` are exact
integers. Float carve-out: the character-sum complex value `U` (unit-modulus phases, analytic size, no
key in the arg path) via FFT — same carve-out as `glv_closure_verification`. `R_S, D_stat, Z` are float
statistics ranked ONLY against integer-count permutation nulls; no float threshold decides a verdict.
`check_no_float.sh` must pass on the coordinate-generation + arg-computation files before any run.

## FALSIFICATION

- **T1a null** iff both strata give `p_S > 0.05` at achieved M_S (detectable ρ ≤ table) AND the positive
  plant fired AND Z is NOT flat. Scoped: "no non-separable diagonal phase coherence beyond the
  symmetry-respecting global null on curves {547,907}, stratum-wise, detectable ρ≤0.057, plant fired."
  A magnitude bound is never written as "no structure"; report the observed R_S and its subspace.
- **T1b.1** has NO pre-judged outcome. Falsification of "the deficit is beyond the marginal shape" =
  `D_stat` inside the two-phase null (`p>0.05`) while significant vs Rayleigh — i.e. the deficit is the
  sub-Rayleigh MARGINAL (revises the −13.99σ INTERPRETATION, not the raw fact). The opposite (survives
  two-phase) leaves the deficit standing as beyond-shape structure.
- **Any run:** flat Z across the 10× N range ⇒ variance miscalibration ⇒ STOP; the reported σ is void.

## PRE-COMMITMENT (filled BEFORE the run)

| outcome | conclusion |
|---|---|
| §0: ΣIm² forced (identity verified), Σ|U|²=n(n−1) | Im-2nd-moment & L²-fidelities EXCLUDED; only phase (T1a) and tail-HM (T1b.1) admissible |
| Positive plant does not fire (either probe) | null uninformative — STOP, fix pipeline |
| Flat Z across 10× N (either probe) | variance miscalibration — STOP, σ void, do not report |
| T1a: R_S ≫ global null (p_S<0.05), Z∝√N, survives OOS all 3 | EXPLORATORY non-separable phase characterization (symmetry type / stratum / subspace), NOT a verdict; fresh confirmatory prereg; grade only after OOS + gate |
| T1a: R_S ≈ global null, plant fired, Z healthy | SCOPED null (per stratum, per curve, detectable ρ stated), conditional phrasing |
| T1b.1: D_stat ≫ two-phase null, survives OOS | deficit is BEYOND the sub-Rayleigh marginal — stands as structure; characterize (which stratum / (b,c)); EXPLORATORY until confirm |
| T1b.1: D_stat inside two-phase null but ≪ Rayleigh null | deficit ATTRIBUTABLE to the sub-Rayleigh marginal shape; revise the −13.99σ interpretation (Rayleigh was the wrong null); the raw sub-Rayleigh fact stands |
| any statistic/null/stratum/(b,c)/curve changed post-scan | deviation — disclose; changed result is EXPLORATORY, never the pre-registered verdict |

**Outcomes are not pre-judged. The frame layers the draft flagged are resolved at object level: phase
is disjoint from the forced 2nd moment (§0), ΣIm² is forced and excluded (§0 derivation), the matched
control is a symmetry-respecting global re-pairing with a mandatory flat-Z tripwire (§T1a.2), and the
deficit is re-scored against a shape-correct null with a negative plant that must stay dark. The run
fills the numbers.**
