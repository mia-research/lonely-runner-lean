# PRE-REGISTRATION — is the sub-Rayleigh deficit μ₃/GLV-graded in the (b,c) frequency grid?

**File:** `PREREG_mu3_glv_frequency_support_v1.md`  **Written:** 2026-08-10, BEFORE any deficit data seen.
**Status:** SPEC ONLY (not a verdict). Drills `RETROSPECTIVE_FINDING_01_subrayleigh_demotion_v1.md`.
**Grade this test can produce:** `[EMPIRICAL — scoped]` at most. No grade promotion of the deficit itself.

Frozen inputs (given, not re-opened): the −13.99σ sub-Rayleigh deficit
`Corr(a₀)=(1/(n−1))·Σ_{(b,c)}|U(a₀,b,c)|` below a random-unit-phase target, one-directional 7/7 primes,
survives the Hermitian-preserving value-multiset null, holds for every character, carried by an ~8%
excess of near-zero harmonics (ρ<0.10). The deficit's EXISTENCE is not under test here — only its
**organization**: is the near-zero excess μ₃/GLV-clustered in the b-frequency, or diffuse?

Forced algebra verified before writing this spec (script:
`scratchpad/verify_conservations_and_power.py` → `partA.py`, `partA4fix.py`, `partB_fast.py`; and the
supplied `verify_U_pullback.py`). Confirmations reproduced inline where load-bearing.

---

## 1. OBJECT

The near-zero harmonics of the single-character array `M_{a₀}(b,c) = |U(a₀,b,c)|`,
`U(a,b,c)=Σ_{d=1}^{n−1} e_p(b·x_d+c·y_d)·e_n(a·d)`, and whether the documented excess of near-zeros
(the deficit's carrier) is **organized by the multiplicative μ₃ action `b ↦ βb`** (β = order-3 element
of F_p*, the GLV-graded direction, `c` fixed), versus diffuse.

This is the object, not a proxy: the deficit *is* the near-zero excess (established), and
"near-zeros cluster within μ₃-orbits of b" is a direct geometric property of the same array.

**Tautology / disjointness check (PASS).** Feature = μ₃-orbit membership of the frequency index b
(pure arithmetic in β; no dependence on |U|). Target = near-zero-ness of `M_{a₀}(b,c)` (a magnitude
property). Disjoint constructions. Critically, they are **not forced-related** at a₀≠0:
- Pullback fixed locus is exactly `{a≡0 mod n} ∧ {b≡0 mod p}` (verified: λ−1 inv mod n, β−1 inv mod p).
- On a deficit-carrying slice a₀≠0, `b↦βb` is NOT a symmetry of |U|: within-triple spread of
  `{M(b,c),M(βb,c),M(β²b,c)}` is mean 5.9 / max 16.6 at p=61 (verified A5), ≠ 0.

So μ₃-membership carries genuine, unforced information about near-zero-ness. Not a tautology.

## 2. STATISTIC (exactly one)

Work on ±-collapsed frequency reps to factor out the FORCED μ₂ (see §3). Partition F_p* into
**μ₆-orbits** `O = {±b, ±βb, ±β²b}` under ⟨β,−1⟩ (size 6, since −1∉⟨β⟩ because |⟨β⟩|=3; verified A7,
count (p−1)/6). Each O contributes three *distinct* magnitude values (the ± pairs are forced equal):
`(M(b,c), M(βb,c), M(β²b,c))` — the **μ₃-triple** at column c.

Define the normalized magnitude `ρ(b,c)=M(b,c)/√(n−1)` (E[ρ²]=1 under the A1 conservation) and the
near-zero label `z(b,c)=1[ρ(b,c)<τ]`, `τ=0.10` **inherited** from the retrospective (pre-committed, not
chosen after looking). For each column c and μ₆-orbit O let `k_{O,c} = z(b,c)+z(βb,c)+z(β²b,c) ∈ {0,1,2,3}`.

**Primary statistic (one number):**
```
   S = Σ_{a₀∈reps} Σ_{c∈Z_p} Σ_{O: μ₆-orbits}  C(k_{O,c}, 2)      (= # near-zero pairs sharing a μ₃-triple)
```
Pooled (NOT a max over cells). Aimed AT the predicted μ₃ subspace; the forced μ₂ is aimed away from
(collapsed into the reps). Integer-valued. Its null distribution is the empirical permutation
distribution under §3's Null-B (mean/variance measured from the permutation, not assumed). Decision
statistic = one-sided Stouffer Z of the per-prime permutation z-scores over the §6 schedule.

**Proof S is not forced (all four verified):**
- (i) μ₃ unforced at a₀≠0 — within-triple spread ≠ 0 (A5); pullback fixes only a≡0∧b≡0.
- (ii) S is invariant to the forced μ₂ (built on ±-reps), so it does not merely re-measure the
  Hermitian symmetry (the prior wrong-null failure mode).
- (iii) l² conservation `Σ_{b,c}M²=p²(n−1)` (verified A1) fixes total energy, not the within-triple
  *tail co-occurrence* (a combinatorial near-zero property) — S is orthogonal to it.
- (iv) per-frequency `Σ_a M²=n(n−1)` (verified A2) constrains across a at fixed (b,c), not within a
  fixed-a₀ triple. S is orthogonal to it.

## 3. MATCHED CONTROL — Null-B (the crux)

**Two nulls, do not confuse them.**
- **Null-A (FROZEN, not this test):** random permutation of the (n−1)/2 conjugate-phase-pairs
  `{e_n(a₀d),e_n(−a₀d)}` across the point-pairs `{(x_d,y_d),(x_d,−y_d)}`. Preserves point set (+its
  φ-structure), phase multiset, Σg(d)=−1, and the Hermitian symmetry g(n−d)=conj(g(d)). This is the
  retrospective's symmetry-matched MC2; it establishes the deficit EXISTS. **It changes the marginal
  near-zero rate** (the deficit is measured against it), so it is the WRONG null for the organization
  question (see FLAG F6).

- **Null-B (THIS test's matched control):** condition on the deficit; test only its μ₃-organization.
  Within each column c, permute the near-zero **labels** across the (p−1)/2 ±-reps (equivalently:
  permute the rep-magnitudes across the μ₃-triples), then recompute S. Repeat to build the null.
  - **PRESERVES:** the exact per-column magnitude multiset ⇒ the per-column near-zero COUNT ⇒ the total
    deficit / marginal rate; the l² conservation (per column, hence A1); the forced μ₂ (labels live on
    ±-reps, so ±b share one label — never split); it never rebuilds U, so U's Hermitian/phase structure
    is untouched (immune to the §2-retrospective wrong-null artifact by construction).
  - **DESTROYS:** only the μ₃-triple grouping of near-zeros — exactly and only the tested alignment.
  - No forced μ₃ structure exists at a₀≠0 (A5), so Null-B destroys nothing forced. It is an exact
    permutation test: under H0 (diffuse) the permutation p-value is uniform; verified calibrated
    (negative control z_total=0.00, §5).

Conditioning on the marginal is mandatory: the character has MORE near-zeros than Null-A (the deficit),
so an unconditioned statistic would fire from the surplus alone, confounding "μ₃-clustered" with "more
near-zeros." Null-B removes that confound.

## 4. PLANTED CONTROL

- **Positive (must fire):** on the character array, depress the three magnitudes of a known number of
  μ₆-orbits below τ (inject within-triple near-zero pairs). S must exceed the Null-B band by the
  predicted amount. Verified: fires (z_total → 10²–10³ for plant_frac ≥ 0.05–0.10, §5).
- **Negative (must NOT fire):** inject the SAME number of extra near-zeros SCATTERED (μ₃-agnostic,
  μ₂-respecting). S must stay inside the Null-B band. Verified: diffuse placement → z_total=0.00 at
  every prime (§5). This is the confound check: S is specific to clustering, not to marginal rate.
- **Discriminant (mechanism-locator, for a positive):** CM curve y²=x³+7 (has GLV φ; point set is
  φ-invariant) vs a NON-CM curve with 3|p−1 (β exists as a field element, but the point set is NOT
  φ-invariant, so μ₃-orbits of b are not a symmetry of the geometry). μ₃-clustering should appear on
  CM and be ABSENT on non-CM. If it fires on non-CM too, S is capturing generic field μ₃, not GLV.
- **A positive's source (secondary):** compute S on Null-A realizations (random Hermitian phases, same
  φ-invariant points). If S(Null-A) already clusters, the effect is a curve/point-set property; if
  clustering is excess over Null-A, it is the character's arithmetic alignment. Both are valid μ₃
  findings; this only localizes the mechanism.

## 5. POWER

Synthetic model (`partB_fast.py`; pure Rayleigh ρ²~Exp(1) + injected clustering, NO real deficit).
All c-columns are statistically identical, so S = Σ over p columns of i.i.d. per-column pair-counts;
z_total = √(rows)·(E[S_col,planted]−E[S_col,null]) / std[S_col,null]. Single character-slice:

| p | reps R=(p−1)/2 | triples/col T | K near-zero/col | Null-B row mean±sd | min detectable *relative* within-triple pairing excess (z_total≥2) |
|---|---|---|---|---|---|
| 2089 | 1044 | 348 | 11 | 0.10 ± 0.32 | ~14% |
| 4093 | 2046 | 682 | 22 | 0.23 ± 0.47 | ~6.4% |
| 8209 | 4104 | 1368 | 44 | 0.46 ± 0.68 | ~3.3% |
| 19231 | 9615 | 3205 | 103 | 1.10 ± 1.04 | ~1.4% |

- **Negative control:** z_total=0.00 at all four primes (Null-B calibrated).
- **Positive control:** fires massively (e.g. p=19231, plant_frac=0.05 → z_total≈+390).
- Pooling over ~24 a-orbit reps divides the detectable excess by ~√24≈4.9 (→ ~3% at p=2089, ~0.3% at
  p=19231); Stouffer over the prime schedule combines further.

**Effect the test resolves at ≥2σ:** a μ₃-clustering that accounts for even a few percent of the
near-zero excess (single slice, large p), sub-percent when pooled. The test is amply powered; the risk
is the opposite (huge n ⇒ tiny biases show as large |Z|), which is why the §9 positive claim requires
the CM/non-CM discriminant and τ-robustness, not |Z| alone. NOTE: the synthetic |Z| assumes a fully
coherent effect + Null-B variance only; the real test uses the EMPIRICAL Null-B, which self-calibrates
to whatever the real per-column variance is (exact permutation test), so the reported p-value is honest
regardless of model mismatch.

## 6. SCOPE

- Curves: CM j=0, `y²=x³+7` over F_p (secp's CM family), `p≡1 mod 6`, `n=#E` prime.
- Prime schedule (feasible per the row_budget lineage to p=19231): **enumerate ALL** prime-order
  curves in windows W = {[2000,2200], [4000,4200], [8100,8300], [16300,16500], [19100,19300]} —
  target ≈ {2089, 4093, 8209, ~16411, ~19231}. **No silent filtering:** every qualifying prime is
  included; if a curve is dropped, log the prime + reason (guards the DRILL-01 "8→3 primes" failure).
  If a window yields <1 curve, widen it by ±200 and log the change.
- Characters: a fixed pre-committed set of **24 a-orbit representatives** (smallest-index reps), SAME
  for every prime (matches the retrospective's 24/24; pooling all n−1 is FORBIDDEN — FLAG F7).
- Threshold: τ=0.10 primary (inherited); τ∈{0.05,0.15} pre-committed robustness (reported, not
  decision-driving).
- Compute: stream per-column (build the p-vector b↦|U(a₀,b,c)| via the x-histogram FFT, accumulate S,
  discard) — memory O(p), feasible to p=19231.

**Every number this run emits inherits this scope and is stated with (curve family, p, a₀-reps, τ).**

## 7. FALSIFICATION (pre-committed, before the run)

Abandon "the deficit is μ₃/GLV-organized" if, at full §6 power:
- pooled Stouffer **|Z| < 3** (near-zeros not μ₃-clustered to the stated power), **OR**
- the CM/non-CM discriminant is inverted (S fires equally on non-CM ⇒ generic field μ₃, not GLV), **OR**
- the sign/significance is not robust across τ∈{0.05,0.10,0.15} (opposite signs or |z|<2 flipping).

Conversely, abandon "the deficit is diffuse" (the current framing) if Z ≥ +5 with the discriminant and
τ-robustness holding.

## 8. EXACTNESS

- Point/index path: exact Python int mod arithmetic (curve add uses `pow(·,p−2,p)`); confirmed by the
  pullback script max|Δ|≈4.4e−15 on the exact-int path. β (mod p), λ (mod n), μ₆-orbits, μ₃-triples,
  the point set: all exact integers.
- Float carve-out (documented, no key in path): the |U| magnitudes (roots of unity, analytic size),
  identical carve-out to `xy_interference_U_v1.py` / `glv_closure_verification`. The threshold
  `ρ<τ` is a monotone map |U|→label ranked against the INTEGER permutation Null-B; S and its p-value
  are integer counts / permutation ranks. No float decides the verdict. Compliant with the no-float rule.

## 9. PRE-COMMITMENT — outcome table (decided now)

| Outcome | Conclusion (scoped: CM y²=x³+7, listed p, 24 a-reps, τ=0.10) |
|---|---|
| Z ≥ +5, CM-only, τ-robust | **The deficit's near-zeros are μ₃/GLV-clustered** — a curve-tied structural handle. `[EMPIRICAL — scoped]`. Report effect size, its p-scaling, and whether it is curve-geometry (S clusters under Null-A too) or character-alignment (excess over Null-A). Restores the deficit as a live, now-*characterized* frontier. |
| \|Z\| < 3 at full power | **SCOPED NULL:** near-zeros are NOT μ₃-multiplicatively-clustered in b at τ, to the stated power (relative excess < the §5 bound). This does NOT say the deficit is structureless — it may live in a subspace this statistic does not project onto (see below). Deficit stays live + mechanism-open (unchanged from frozen status). |
| Z ≤ −5, CM-only, τ-robust | **μ₃-DISPERSION:** near-zeros avoid sharing μ₃-triples — a different but real organization. Report as a finding; do not call it "diffuse." |
| 3 ≤ \|Z\| < 5, or discriminant/robustness mixed | **INCONCLUSIVE.** Extend the prime schedule; report as inconclusive. No claim either direction. |

**Subspaces this statistic does NOT project onto** (so a null is scoped, never "structureless"): the
c-coordinate organization; ADDITIVE (not multiplicative) b-structure; the curve-tied diagonal c=±b
(the xy_interference test-3 axis — a non-μ₃ structure); higher μ₃-moments beyond the ≥2-near-zero
co-occurrence (e.g. phase/argument alignment within triples). A null on S licenses none of these.

---

## FLAG — forced / uninformative variants of the proposed design (and why)

- **F1 — Full diagonal D-orbit binning** `(a,b,c)↦(λa,βb,c)`: |U| is exactly constant within (the
  pullback), so within-orbit var|U|²≡0. Measures nothing. (The trap named in the task.)
- **F2 — Per-μ₃-class TOTAL-deficit comparison** (class X's Σ|U| vs class Y's): by the duality
  |U(a₀,βb,c)|=|U(λ⁻¹a₀,b,c)| (verified A4) plus multiset-equality across the a-orbit (verified A6),
  the total deficit is **forced equal** on each a-μ₃-orbit; a class-vs-class total contrast reduces to
  comparing a-slices and is forced. Uninformative. (The proposed "deficit within μ₃-orbits vs generic
  orbits" collapses to this if read as a per-class total — hence the §2 statistic is a *within-triple
  co-occurrence*, not a per-class total.)
- **F3 — μ₃-fixed (b=0) vs free split:** b=0 is the pure-y channel; its apparent deficit was a
  documented **wrong-null artifact** (retrospective §2: on-axis −10% collapsed to −0.1..−3.8% under the
  Hermitian-matched null), and it is forced-equal across the a-orbit. Not the μ₃ story; artifact risk.
- **F4 — Max-over-μ₃-cosets** ("which coset is most enriched"): max over many noisy cells,
  upward-biased, low power. Banned by the pooled-statistic rule; §2 uses a pooled sum.
- **F5 — Justifying the fixed-a₀ b↦βb binning BY the GLV pullback: WRONG (task constraint 3).** The
  pullback relates (a₀,b,c) to (λ⁻¹a₀,b,c) — a DIFFERENT a-slice; at fixed a₀ the μ₃-triple is |U| at
  three different characters and is UNFORCED (A5). Correct justification = the multiplicative μ₃
  structure on the frequency b + φ-invariance of the point set, tested against the marginal-preserving
  Null-B. Never "GLV is a symmetry so bin by it."
- **F6 — Using Null-A (phase permutation) for the organization question:** Null-A changes the marginal
  near-zero rate (it is the null the deficit is measured against), so S-vs-Null-A fires from the deficit
  itself, confounding μ₃-clustering with the marginal surplus. Must use Null-B (marginal-preserving).
- **F7 — Pooling over all n−1 characters:** triple-counts are forced identical within each a-μ₃-orbit
  (A4/A6), so pooling all characters triple-counts the same values → fabricated 3× "power" / broken
  independence. Pool a-orbit REPS only (§6).
- **F8 — Within-triple VARIANCE of |U|² as the statistic:** unforced (fine) but dominated by the
  bulk/high tail, not the near-zero tail that carries the deficit — low power for THIS effect. §2 uses
  the tail-focused near-zero pair-count instead.

---
*Reproduce forced-structure claims: `partA.py` (A1–A7), `partA4fix.py` (duality with correct
inverse λ⁻¹=λ²), `partB_fast.py` (calibration + power). All use exact-int point paths; float only in
|U| magnitudes.*
