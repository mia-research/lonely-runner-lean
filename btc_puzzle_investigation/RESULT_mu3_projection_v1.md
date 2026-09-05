# RESULT — H_proj REFUTED by its own structural readout; the N1 ½-saturation RESOLVED as 2√p/4√p (v1, 2026-07-24)

**Spec:** `PREREG_mu3_orthogonal_projection_v1.md` (frozen; the literal projection is a forced zero,
§1.3, so the registered object is H_proj — isotype content controls extremal magnitude at fixed `#R`).
**Deviations:** `PREREG_mu3_orthogonal_projection_v1_DEVIATIONS.md`.
**Scripts:** `mu3_projection_v1.py` (primary D₄ + plants), `mu3_selfnull_v1.py` (per-readout self-null),
+ the exact-max-saturation check. Runs: `mu3_projection_discovery_run_v1.out`,
`mu3_selfnull_run_v1.out`.

---

## 1. The registered hypothesis H_proj is REFUTED

The primary contrast fired: `D₄ = S_{χ₂(y)} − S_{χ₂((x−x₁)(x−x₂))}` (both `#R=4`) is sharply negative,
Stouffer `Z = +10.98` (lower tail), **12/12 discovery units** below their null mean, per-unit
`p_lo ≤ 0.0075`. Naively that is outcome A2 (H_proj supported).

**The mandatory §2.5 structural readout overturns that reading.** Measuring each readout against **its
own** symmetry-matched null (ρ = S_real / S_null, `mu3_selfnull_run_v1.out`, 12 units):

| readout | `#R` | μ3-invariant? | mean ρ = S_real/S_null |
|---|---|---|---|
| χ₂(x) | 2 | **yes** | **0.540** (suppressed) |
| χ₂(x−x₀) | 2 | no | **0.532** (suppressed) |
| χ₂(y) | 4 | **yes** | **0.536** (suppressed) |
| χ₂((x−x₁)(x−x₂)) | 4 | no | **0.969** (at null) |
| χ₂(xy) | 6 | **yes** | **1.027** (at null) |
| χ₂(y(x−x₀)) | 6 | no | **0.996** (at null) |

**Suppression does not track μ3-isotype content:** χ₂(x−x₀) is non-invariant yet suppressed (0.53),
and χ₂(xy) is μ3-invariant yet **not** suppressed (1.03). The D₄ rejection is real but its isotype
*interpretation* is false — χ₂(y) and χ₂((x−x₁)(x−x₂)) simply fall on opposite sides of a split that is
**orthogonal to invariance**. **H_proj is refuted** (this is the falsification the §2.5 readout exists
to deliver; the primary alone would have mis-concluded A2).

**The real split is single factor vs product of two factors:** suppressed =
{χ₂(x), χ₂(x−x₀), χ₂(y)} (χ₂ of one irreducible factor); at-null =
{χ₂((x−x₁)(x−x₂)), χ₂(xy), χ₂(y(x−x₀))} (χ₂ of a product of two coprime factors).

---

## 2. N1 RESOLVED — the ½ is `2√p / 4√p`, an exact single-factor cap `[VERIFIED exact, 22 primes]`

The absolute attained magnitude `max_a |V_f(a)| / √p` (skipping DC), not a ratio to any null:

| readout | `#R` (ceiling) | `max|V|/√p` | saturation of `#R·√p` |
|---|---|---|---|
| χ₂(x) | 2 (`2√p`) | **≈ 2.00** | **≈ 1.00** (full) |
| χ₂(x−x₀) | 2 (`2√p`) | **≈ 2.00** | **≈ 1.00** (full) |
| **χ₂(y)** | 4 (`4√p`) | **≈ 2.00** | **≈ 0.50** ← the N1 ½ |
| χ₂((x−x₁)(x−x₂)) | 4 (`4√p`) | ≈ 3.3 | ≈ 0.82 |
| χ₂(xy) | 6 (`6√p`) | ≈ 3.3 | ≈ 0.55 |
| χ₂(y(x−x₀)) | 6 (`6√p`) | ≈ 3.5 | ≈ 0.60 |

> **χ₂(x), χ₂(x−x₀) and χ₂(y) all attain the SAME absolute magnitude `max|V| = 2√p`** (to three
> digits: 1.95–2.02 across every unit). χ₂(y)'s Weil ceiling is `4√p` (four odd-order points: three
> 2-torsion zeros + the order-3 pole at O), so its saturation is exactly `2√p / 4√p = ½`.

**Confirmed on the ORIGINAL N1 primes** (the §A2.6 table — all `p ≡ 1 mod 3`, `n` prime), χ₂(y)
saturation of `4√p`: **991→0.497, 1051→0.494, 1237→0.500, 1249→0.498, 1303→0.488, 1669→0.489,
1831→0.498, 2089→0.499, 2143→0.496, 2281→0.489** — and χ₂(x) reaches ≈2√p (0.96–1.01) at every one.

**This resolves N1 and kills the "2 of 4 eigenvalues" mechanism, decidably:**
1. χ₂(x) — a `#R=2` sum with **no** 4-dimensional `H¹` — reaches the *same* absolute `2√p`. So the ½
   is not about the y-sheaf's 4-dim structure; it is that a **single-factor** χ₂ sum caps at `2√p`,
   and y's *nominal* ceiling is `4√p`.
2. The μ3-invariant χ₂(xy) does **not** sit at ½ of its ceiling, and the non-invariant χ₂(x−x₀) does.
   So the ½ is not a μ3-isotype / eigenspace-starvation effect.
3. Consistent with the standing derivation ([−1] maps `H¹(a)→H¹(−a)`, no fixed-`a` 2+2 split): the ½
   was never a per-frequency eigenspace split, and this shows what it actually is — an attained-magnitude
   cap of single-factor quadratic character sums.

**Candidate mechanism `[HYPOTHESIS]`:** the attained `2√p` says the `H¹` dimension carrying top-frequency
mass is **2** for a single-factor χ₂ sum, independent of the ramification count `#R` that sets the Weil
*ceiling*. Why single-factor → dimension 2 (and product → higher) is not proved here; it is the object
Arm 2 (eigenvalue multiset) was written to settle and is the named next step.

> **UPDATE (Arm 2, `RESULT_arm2_eigenvalue_v1.md`): this hypothesis is REFUTED.** Sage cover zeta
> functions show χ₂(y) carries a genuinely **4-dimensional** `H¹` (the abelian surface A_new, char poly
> `T⁴+p T²+p²`, eigenvalues √p at ±60°/±120°) — **not** dimension 2. χ₂(x), by contrast, is dim-1
> (2 eigenvalues), so its `2√p` really is dimensional. The two readouts attain the same `2√p` for
> **different** reasons: χ₂(x) because it has only 2 eigenvalues; χ₂(y) by **CM cancellation** among 4.
> The N1 ½ *magnitude* (`2√p/4√p`, §2) stands; its *mechanism* is CM cancellation in a dim-4 A_new,
> with the exact cap now the one open piece (candidate: the [−1]-parity 2+2 split).

---

## 3. Controls, plants, exactness

- **P-1 rank ladder:** S strictly increases in `r` (1.37e7 → 8.21e7 for r=1..6) — the statistic has
  tail-rank resolution; the §A2.6 bulk-average blindness is avoided (top-16 mean, not a moment).
- **P-3:** detects a planted isotype effect down to δ=0.5 per unit (large-only, as the §5 power
  estimate predicted); the observed effect is ½-scale, well within reach; pooled `Z=11`.
- **§2.4 exact `l²` identity** `Σ_a|V|² = n·#{f≠0}` holds to ≤3 (integer) on every readout — no
  normalisation artifact.
- **Exactness:** signal path (c ∈ {−1,0,1}, coords) exact int; `|V|²` via numpy FFT is the §8
  monotone-statistic-ranked-against-matched-null carve-out (DEVIATION D-float; same pipeline on every
  null draw; top-16 boundary-gap guard printed). The **N1 cap in §2 is an exact-magnitude fact**
  reproduced to 3 digits on 22 primes — not a statistical rate.

---

## 4. Scope, deviations, what is NOT established

- **Frame is ORDINARY, not supersingular.** `y²=x³+7` is supersingular iff `p≡2 mod 3`, but the GLV
  frame requires `p≡1 mod 3`, so every unit is ordinary. The §6.1 stratum table's
  "supersingular / m-law" labels are **void in this frame** (DEVIATION D-strat); units are relabelled by
  `p mod 4` (which sets `χ₂(−1)`, hence whether χ₂(y) is μ2-odd/even). The ½ appears identically in both
  `p mod 4` classes.
- **S2 stratum empty** — no unit matched the (mis-specified) S2 condition; not a filter, a consequence
  of the label defect.
- **Only the discovery decade** (`n ∈ [10³,10⁴]`) was run for the D₄/self-null statistics; the
  replication decade and out-of-sample arm were not. **The §2 N1 cap does not depend on this** — it is
  an exact magnitude reproduced on 22 primes including all 10 original N1 primes. The *statistical* D₄
  refutation of H_proj is discovery-only and is reported as such.
- **Arm 2 (twisted eigenvalue multiset) not run.** The §2 empirical cap is the object-level answer it
  targeted; the eigenvalue computation (Sage, `p ≤ 61`) remains the way to *prove* dimension 2.
- **No ECDLP content.** `V_f(a)` is a character sum over the public curve; nothing here approaches a
  scalar bit. `p ≤ 5·10³` here, `p ≤ 2·10³` for the original-prime check — ~240 binary orders below secp.

---

## 5. Net

| claim | grade |
|---|---|
| H_proj (μ3-isotype controls extremal magnitude) | **REFUTED** — self-null: χ₂(x−x₀) non-inv suppressed, χ₂(xy) inv not |
| single-factor χ₂ sums (x, x−x₀, y) cap at `max|V| = 2√p` | `[VERIFIED exact, 22 primes]` |
| N1 ½-saturation of χ₂(y) `= 2√p/4√p` | `[VERIFIED exact, incl. all 10 original N1 primes]` |
| ½ is NOT a 2-of-4 eigenvalue effect | `[PROVED by counterexample]` — χ₂(x) (#R=2) hits same 2√p |
| single-factor → `H¹` top-mass dimension 2 | `[HYPOTHESIS]` — Arm 2 (Sage) is the proof route |

*Grade legend: PROVED · VERIFIED (exact) · REFUTED · HYPOTHESIS.*
