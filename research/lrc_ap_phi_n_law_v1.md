# The φ(n) Law for Arithmetic Progressions in the LRC — repo record (v1)

**Filed 2026-07-23.** This document had **no presence in this repository** before today, despite being
a published Zenodo record and the origin of the φ(n)-residue line. Record created so the content is
greppable; the paper itself is `lrc_ap_phi_n_law_v1.pdf` (8 pp).

| | |
|---|---|
| **Title** | *The φ(n) Law for Arithmetic Progressions in the Lonely Runner Conjecture: Algebraic Structure and Computational Fragility* |
| **Type** | Research Summary / whitepaper |
| **Dated** | 2026-01-06 (Zenodo record 2026-01-04) |
| **DOI** | `10.5281/zenodo.18158886` (working paper) |
| **PDF** | `lrc_ap_phi_n_law_v1.pdf`, SHA-256 `8a4a115fac14eae1714823b1226036d2caa75d23e298b249f5e57f8dfe3d7343` |
| **Memory** | recorded in `zenodo_preprint_record_2026_07_10.md` as the "bridge paper … origin of the φ(n)-residue idea" |

**Relationship to the rest of the project — distinct from the n=11 work.** This is *not* part of the
`lrc_n11_*` / `eleven_lonely_runners*` lineage, which proves classical LRC for `n = 11` via
Complementary Pairs + the Coupling Principle. This paper treats a **measure-zero subcase for general
`n`**: speeds in exact arithmetic progression with common start. It is also the acknowledged origin of
the **φ(n)-residue** idea that later runs through the RH / L-function programme (see the Zenodo memory).
Note that the `btc_puzzle_investigation/phi_n_*` files are an unrelated secp/BTC thread despite the name.

---

## Scope, as the paper itself states it

APs are a **measure-zero subset** of all speed configurations — "an infinitesimally small fraction of
the space of all speed assignments." The paper's claim is a structural law for that family, explicitly
**not** a general-`n` result. `n ≤ 7` is attributed to Barajas–Serra 2008 and `n = 8` to Rosenfeld 2025
(arXiv:2509.14111, computer-exhaustive).

## Main results

**Theorem 3.1 (φ(n) Isolation Law for APs).** For `n` runners with speeds `v_i = v₀ + (i−1)δ` starting
at the same position:
- (a) Perfect isolation — gap exactly `1/n` — occurs at the discrete times `t` with `{δt} = r/n` and
  `gcd(r, n) = 1`.
- (b) Within each phase period of `{δt}` there are exactly **φ(n)** such isolation instants.
- (c) At these instants the positions form a translate of the uniform `n`-grid.
- (d) Hence APs with common start satisfy the LRC (existence of isolation).

*Mechanism:* `j ↦ jr (mod n)` is a permutation of `{0,…,n−1}` iff `gcd(r,n) = 1`; the count of such `r`
is Euler's totient. `{v₀t}` contributes only a rotation and does not affect relative spacings.

**Lemma 3.2 (Spectral characterization).** For `μ_t = (1/n)Σ_j δ_{p_j(t)}`, the configuration is a
translate of the uniform `n`-grid **iff** `μ̂_t(k) = 0` for all `k ≢ 0 (mod n)` (and
`μ̂_t(k) = e^{−2πikv₀t}` when `n | k`). At perfect-isolation times all non-trivial Fourier modes
vanish — an independent route to the same instants.

**Proposition 4.1 (Zero-radius fragility).** For AP speeds with common start, the property "there exists
`t` with configuration a uniform `n`-grid" has **zero stability radius**: exact grid formation imposes
`n−2` independent linear congruences, a measure-zero affine set, so arbitrarily small perturbations
destroy it.

**Boundary Set Method (§2.2, Lemmas 2.1–2.2, Algorithm 2.1).** Isolation status can only change at the
critical times `t = (k ± 1/n)/Δv`; between consecutive boundary times the predicate `f_i(t) ≥ 1/n` is
constant. Gives an **event-complete** evaluation procedure. Complexity: `M(H) = Θ(Hδn³)` boundary times,
evaluation `O(Hδn⁴)`.

## Empirical validation (7,287 configurations)

| | result |
|---|---|
| arithmetic progressions | **5,291 / 5,291** perfect φ(n) correlation (100.000%) |
| non-arithmetic families | **0 / 1,996** φ(n) matches (0.000%) |
| Wilson 99.9% CIs | [99.796%, 100.000%] vs [0.000%, 0.540%] |

Tolerances are ulp-aware: `τ_gap = max(10⁻¹², 16·ulp(1/n))`, `τ_phase = max(10⁻¹², 16·ulp(r/n))`.

## Resolution of the n = 8 computational anomaly (§6)

Prior studies reported systematic AP tests succeeding while randomly generated "APs" frequently failed.
Root cause: random parameter generation introduces floating-point deviations from exact AP structure,
and by Prop 4.1 those are **sufficient to destroy** the algebraic identity. The failures were therefore
**confirmations of the law's zero-radius fragility, not counterexamples to it.** Exact `n = 8` APs
satisfy the `φ(8) = 4` law across tolerances `10⁻¹²`–`10⁻⁶`, with isolation phases at `{1,3,5,7}·T/8`.

---

## Reading notes / caveats worth carrying

1. **Measure-zero scope is the paper's own framing**, stated in §1.3 and §7 — this is a structural law
   for a special family plus an anomaly resolution, not progress on general-`n` LRC. Do not let the
   "Constructive LRC proof" bullet in §7 be quoted without the AP restriction attached.
2. **The empirical section is float-based** (IEEE-754 with ulp-aware tolerances), which is the paper's
   own subject matter — fragility at the precision level. It predates and is outside this project's
   later no-float-in-signal-path rule (`btc_puzzle_investigation/CLAUDE.md`); that rule was written for
   key-derived arithmetic, and the tolerance framework here is the object of study rather than a
   contaminated measurement. Flagged so the two are not confused.
3. **Prop 4.1's proof is a sketch** in the paper ("Proof Sketch"), not a full proof.
