# PREREG — locus of the sub-Rayleigh near-zero |U| excess in the c-channel / joint (b,c)

**File:** `PREREG_subrayleigh_deficit_locus_c_channel_v1.md`  **Frozen:** 2026-08-22
**Status: PRE-RUN.** No statistic in §2–§9 has been computed. The only code executed while
writing this spec was (i) a `p % 3` check over the 30 frozen primes (all `≡ 1 mod 3`,
verified — so `β ∈ F_p` and the μ₃/μ₆ strata are in scope at every model prime) and
(ii) a closed-form power arithmetic on stratum sizes. Neither touches an arm statistic.

This is a **CHARACTERIZATION of an established positive** (the near-zero `|U|` excess), NOT a
test of its existence and NOT a verdict. Per the Anomaly-Drill protocol it must end in a
sharper law / a named subspace / a bounded magnitude / a next probe — **never a closure of N7.**
A clean "the excess is isotropic across the tested organizers to power [x]" is a valid,
valuable output (branch B, §9).

---

## 0. SCOPE BANNER (inherited by every number this run produces)

Enumerable model curves `E : y² = x³ + 7` over `F_p`, `p` in the frozen 30-prime list of §7,
prime group order `n = #E(F_p)`, canonical generator `G`, `d = 1..n−1` fully enumerated,
character `a₀ = 1`. `p = 2²⁵⁶ − 2³² − 977` is **not** enumerable and **nothing here transfers
there** — every object is a full group sum over all `d`. **NO ECDLP / extraction / security
claim** is made or may be derived from any outcome. Model range only.

---

## 1. OBJECT

Inherited exactly from `PREREG_subrayleigh_deficit_locus_v1.md` (§1) and the established
positive (Stouffer `−71.80` over these 30 primes, one-directional, replication-gated):

```
U(b,c) = Σ_{d=1}^{n−1} e_n(a₀ d) · e_p(b x_d + c y_d)      (b,c) ∈ [0,p)²,  a₀ = 1
σ̂²     = p²(n−1)/(p²−1)         (Fraction; = mean_S |U|², exact, both arms)
r(b,c) = |U(b,c)| / σ̂           (E[r²] = 1 exactly)
S      = {(b,c) ≠ (0,0)}
```

**The object measured here is the LOCUS on the `(b,c)` frequency grid of the established
near-zero `|U|` excess** — i.e. *where* the extra near-zero cells (`r < τ`) sit, stratified by
the OPEN symmetry organizers (c-direction μ₂, the `c=±b` diagonal, the joint `(b,c)` μ₆
orbit). We do **not** re-test that the excess exists; we localize it.

**Exact self-symmetry of the `a₀`-grid (load-bearing).** `e_n(a₀(n−d)) = conj(e_n(a₀ d))`, so
the character grid is Hermitian and `|U(b,c)| = |U(−b,c)|` **exactly** (even in `b`; derived,
matches `PREREG_..._locus_v1` §7 equivariance). This is the ONLY self-symmetry at fixed `a₀`.
The maps `c ↦ −c` and `b ↦ βb` are **NOT** self-symmetries of the `a₀`-grid — they relate `a₀`
to the *other* characters `−a₀` and `λa₀` (equivariance, `..._locus_v1` §7; ADD3-A caution).
Therefore c-sign and μ₃/μ₆ strata are **genuinely testable, non-tautological** organizers.

**Tautology check.** Stratum membership is a function of the frequency indices `(b,c)` and the
curve geometry ONLY (axes, diagonal `c=±b`, μ₆ orbit `{(β^i b, ±c)}`); the near-zero indicator
`r<τ` is a function of the character phase. Feature (geometric stratum) and target (phase-driven
near-zero) share only the grid, not construction — this is not a residue-vs-component tautology.
The one exact symmetry that COULD manufacture spurious pair-concordance is `b ↦ −b`; it is
**folded out** (§3) before any co-occurrence statistic runs.

---

## 2. STATISTIC — one primary, named now

Work on the **folded fundamental grid** `F = {(b,c) : b ∈ {0,…,(p−1)/2}, c ∈ {0,…,p−1}} \ {(0,0)}`.
Folding `b ↦ −b` uses the exact self-symmetry: each `|U|` value appears once in `F`. All counts,
z-scores, χ², and permutation p-values are computed over `F`; the matched-null ensemble supplies
every variance empirically. **No analytic variance is assumed anywhere** (this is the mechanical
guard against the ADD3-C block-independence miscalibration).

**Near-zero indicator:** `Z_τ(b,c) = [ r(b,c) < τ ]`, decided on the float magnitude but never
verdict-bearing by itself (only ranks of the resulting integer counts against the null decide —
§8). **τ-set (frozen, inherited from ADD3-B/C):** `τ ∈ {0.05, 0.10, 0.15}`
(null near-zero fractions `f_τ ≈ {0.0025, 0.00995, 0.02225}`, Rayleigh). A verdict requires
concordance across the τ-set; a signal at one τ only is flagged as a threshold-boundary
artifact, not a finding.

**PRIMARY statistic — the LOCATION isotropy χ² (single verdict-bearing scalar).**
Primary partition `P` of `F` into 5 disjoint strata covering `F` (exact, verified in §3):

| stratum | definition (`b∈{1..(p−1)/2}` unless noted) |
|---|---|
| `Σ_baxis` | `c = 0` |
| `Σ_caxis` | `b = 0`, `c ≠ 0` |
| `Σ_diag`  | `c ∈ {b, p−b}` (the `c = ±b` diagonal) |
| `Σ_cpos`  | `c ∈ {1..(p−1)/2}`, `c ≠ b`  (bulk, c-positive half) |
| `Σ_cneg`  | `c ∈ {(p+1)/2..p−1}`, `c ≠ p−b`  (bulk, c-negative half) |

For stratum `s`: near-zero count `K_s = Σ_{(b,c)∈s} Z_τ(b,c)` (exact integer). Global excess
density `δ̂ = (K_tot − Ê_null[K_tot]) / N_tot`. Primary statistic

```
X² = Σ_{s∈P} ( K_s − Ê_null[K_s] − δ̂·N_s )² / V̂_null[K_s]
```

with `Ê_null`, `V̂_null` from the matched Hermitian ensemble (§4). Under **isotropy** (the excess
is uniform per cell), `X² ~ χ²_{|P|−1} = χ²_4`; the verdict uses the **exact permutation
p-value** = rank of the real `X²` among the `R` null replicates' `X²` (float-free verdict).
Per-stratum signed contribution `z_s = (K_s − Ê_null[K_s] − δ̂·N_s)/sd_null(K_s)` names WHICH
stratum concentrates the excess. This partition tests axes / diagonal / c-sign LOCATION; it does
**not** stratify by μ₃-`b` (the excluded ground, ADD3-B) — that is handled, partialled-out, in
the secondary μ₆ test.

**SECONDARY targeted statistics** (each aimed AT one open organizer; reported with the primary,
never a lone verdict):

- **S-C2 (c-sign asymmetry, location):** signed contrast `D_c = K_cpos − K_cneg`; `z` vs the
  Hermitian ensemble. Tests `c ↦ −c` location asymmetry.
- **S-Cpair (c-μ₂ organization, co-occurrence — VARIANCE-type, ADD3-C danger):** restricted to
  bulk, `Q_c = #{(b,c): b∈{1..(p−1)/2}, c∈{1..(p−1)/2}, c≠b, Z_τ(b,c)=Z_τ(b,p−c)=1}`
  (near-zero co-occurrence across the `c↦−c` pairing at fixed `b`). Null: the marginal-preserving
  / global-repartition null of §4 (**NOT** the Hermitian ensemble — see §4 "marginal-rate
  confound").
- **S-mu6 (joint (b,c) μ₆ organization, co-occurrence — VARIANCE-type):** for each generic bulk
  μ₆ orbit `O = {(β^i b, ε c) : i∈{0,1,2}, ε∈{±}}` (6 folded cells), the **cross-sign (twist)
  near-zero pair count** `T_μ6 = Σ_O Σ_{i,j} Z_τ(β^i b,+c)·Z_τ(β^j b,−c)`. Null: **within-(orbit,
  sign) marginal-preserving permutation** — permute which b-slots are near-zero inside each
  size-3 `(orbit,sign)` block, holding the per-block count fixed. This holds the **excluded μ₃-`b`
  marginal AND the c-sign marginal exactly** and destroys only the cross-sign twist alignment.
  This isolates the NEW μ₆ content (the c-coupling) from ADD3-B's already-excluded μ₃-`b`
  content; we do not re-litigate ADD3-B.

The four organizers OVERLAP (a cell can be on the diagonal AND in a size-6 μ₆ orbit; μ₃-`b`
cuts across the bulk). They are reported **separately**; no joint-independence is claimed. This
non-orthogonality is a frame item, flagged in §10.

---

## 3. PARTITION EXACTNESS (self-audit item a, resolved here)

`P` is a genuine disjoint cover of `F \ {DC}`: for `b=0` the only non-DC cells are `Σ_caxis`;
for `b∈{1..(p−1)/2}`, `c` ranges `{0}` (`baxis`) ∪ `{b,p−b}` (`diag`) ∪ `{1..(p−1)/2}\{b}`
(`cpos`) ∪ `{(p+1)/2..p−1}\{p−b}` (`cneg`) = all of `{0..p−1}`. `p` odd ⇒ `(p±1)/2` integers,
`b` and `p−b` distinct (fold is clean, no fixed point since `n` prime ⇒ odd). **No cell is
counted twice; the excluded μ₃-`b` GLV structure is never in the primary partition** — the
primary tests axes/diagonal/c-sign only, and the μ₆ secondary explicitly partials the μ₃-`b`
marginal out. Verified by construction; a run-time assertion `Σ_s N_s == |F|−1` and
`disjoint(P)` must print `True` before any count is read.

---

## 4. MATCHED CONTROLS — what is preserved, what is destroyed

**MC-H — matched Hermitian null (PRIMARY for the LOCATION statistic X² and S-C2).**
`g(n−d) = conj(g(d))`, unit modulus, uniform random phase on a fundamental set of the
`(n−1)/2` `{d, n−d}` pairs (no fixed point: `n` prime ⇒ odd). *Preserves:* the point set
`{(x_d,y_d)}`, the grid geometry (which cells are axes / diagonal / μ₆-orbit), `p`, `n`, `|g|=1`,
`Σ_d g(d) = −1`, and the **exact self-symmetry** `|U(b,c)|=|U(−b,c)|` (so null draws fold
identically). *Destroys:* only the arithmetic AP phase `e_n(a₀ d)`. `R = 200`.
This is the correct null for X² and S-C2 because the **isotropy** statistic differences the
global excess out (`δ̂·N_s`), so it is NOT confounded by the marginal excess; it isolates
NON-uniform concentration.

**MC-GR — marginal-preserving / global-repartition null (PRIMARY for the co-occurrence
statistics S-Cpair, S-mu6).** Fix the REAL near-zero set (its exact count per conditioning
block), and randomly repartition which grid positions carry the near-zero label, preserving the
folded `b↦−b` structure and the block marginals named per test (S-Cpair: per-`b`-row near-zero
count; S-mu6: per-`(orbit,sign)` near-zero count), destroying only the pairing / twist
alignment. `R = 200`. **Why MC-H is the WRONG null for co-occurrence (the marginal-rate
confound):** real has ~8% MORE near-zero cells than an MC-H draw, so a raw co-occurrence count
in real exceeds MC-H's *trivially* from the higher marginal rate — that would fire on the
already-established global excess, not on new c/μ₆ organization. MC-GR fixes the real near-zero
COUNT and only scrambles positions, removing this confound. This is the ADD3-C correction made
structural.

**Why an analytic per-block null is banned here (the ADD3-C lesson, stated as a rule).** The
ADD3-C `+10.36` was a variance artifact: an analytic per-block null pooled correlated `(a₀,c)`
blocks as independent, underestimating variance ~2.85×. **Every variance in this spec is
empirical** — from MC-H (location) or MC-GR (co-occurrence) — so a block-independence
assumption cannot enter.

---

## 5. PLANTED POSITIVE CONTROLS — all must fire before any verdict

| id | plant (L2-conserving where it mimics the real effect) | must fire in | pass criterion (printed) |
|---|---|---|---|
| **P1 (diag concentration)** | redistribute `|U|²` WITHIN `Σ_diag`: push a known fraction `π₀=0.5` of diagonal cells below `τ`, compensate a matched diagonal set upward so `Σ_diag|U|²` is **conserved to ≤1e−9 rel** (Parseval-faithful, localized) | X² + `z_diag` | permutation p `< 1/(R+1)` AND `z_diag = max_s z_s` AND recovered diagonal excess within ±20% of planted |
| **P2 (c-sign asymmetry)** | inject a signed near-zero surplus into `Σ_cpos` only, nominal `D_c` shift `+3 sd` | S-C2 | `z_{D_c} > +5` |
| **P3 (c-pair alignment)** | force `Z_τ(b,c)=Z_τ(b,p−c)` on a known set of bulk c-pairs (planted twist), nominal `Q_c` excess `+5 sd` vs MC-GR | S-Cpair | `z_{Q_c} > +5` vs MC-GR |
| **P4 (μ₆ twist)** | force cross-sign near-zero alignment in a known set of μ₆ orbits, μ₃-`b` marginal untouched | S-mu6 | `z_{T_μ6} > +5` vs MC-GR |
| **P5 (uniform-excess NEGATIVE-for-concentration)** | inject the ~8% near-zero excess **uniformly** (rate-only, no locus): X² must **NOT** trip | X² | permutation p `> 0.05` at every τ (isotropy holds under a pure rate effect) |

**If any of P1–P4 does not fire, the corresponding arm reports "planted control did not fire;
null uninformative" and issues no verdict.** If **P5 trips X²**, the isotropy statistic has a
rate-leak (df or `δ̂` misspecified) and X² is void until fixed — the plant that must *fail* is
as load-bearing as the plants that must fire.

**Forced readout checks (zero evidence, must print):**
- **E1 (Parseval, integer).** `Σ_S |U|² == p²(n−1)` for char and every null draw, `≤1e−9` rel.
- **E-fold.** assert `|U(b,c)| = |U(−b,c)|` to `≤1e−11` on a random cell sample (validates the
  fold; a failure is a bug, not a finding).
- **E-β.** `β` derived from the data as an order-3 element with `max_d ((β·x_d mod p) − x_{λd}) `
  ` == 0` as an **exact integer assertion** (the paired `(λ,β)` derivation that the `..._locus_v1`
  run's `p=433/577` bug requires); no μ₆ statistic runs before this passes.

---

## 6. NEGATIVE / VARIANCE-ARTIFACT CONTROLS (the ADD3-C guard)

- **NC-floor (null-vs-null).** Score one MC-H draw's full pipeline (X², S-C2, S-Cpair, S-mu6)
  against the rest of the ensemble / its own MC-GR null. Required: X² permutation p ~ Uniform,
  per-stratum `z_s ~ N(0,1)`, `z_{Q_c}, z_{T_μ6} ~ N(0,1)`. **If null-vs-null fires, the
  statistic is miscalibrated and the arm is void** regardless of the real number.
- **NC-√N (the exact ADD3-C diagnostic).** Across the 30 primes (`n` spans ~80×), a GENUINE
  per-stratum concentration of fixed density gives per-prime `z(n) ∝ √N_s` (grows with `n`); a
  variance artifact gives `z(n)` **flat in `n`**. Pre-registered rule: for every arm, plot
  per-prime `z` vs `n`; **a flat `z(n)` VOIDS that arm's pooled Stouffer** (this is precisely the
  tell that caught ADD3-C's `+10.36`). A real signal must show `z(n)` rising with `n`.

---

## 7. SCOPE

**Primes (frozen 30, all verified `≡ 1 mod 3` ⇒ `β ∈ F_p`, μ₃/μ₆ strata valid at every one):**
`151,193,211,241,277,349,397,433,523,619,691,823,937,1093,1249,1471,1693,1987,2281,2671,3169,`
`3607,4177,4861,5647,6571,7639,8893,10357,12043`. `a₀ = 1`. `R = 200`.
The **pooled Stouffer over all 30** is the powered statistic for the thin strata (§8); individual
small primes are underpowered on axes/diagonal and must not be read alone. Bulk / c-sign have
per-prime power at the larger primes.

---

## 8. POWER — computed now (τ = 0.10, `f = 0.00995`; `δ_global = 0.08·f = 7.96e−4` absolute
near-zero-fraction excess if uniform)

Detectable ABSOLUTE per-stratum excess-density DEPARTURE `Δδ_s` (departure from the uniform
`δ_global`), empirical-sd model `sd(K_s) ≈ √(f(1−f)N_s)` (ensemble supplies the true sd; the
correlation-inflation factor `ρ` is measured at run and reported — this floor assumes `ρ≈1`):

| stratum | `N_s` scale | per-prime `z=3` `Δδ_s^min` @ `p=12043` | **pooled(30) `Z=5` `Δδ_s^min`** |
|---|---|---|---|
| `Σ_diag`  | `≈ p`    | `2.7e−3` (3.4× δ_global) | **`2.0e−3` (2.5× δ_global)** |
| `Σ_caxis` | `≈ p`    | `2.7e−3` (3.4×) | **`2.0e−3` (2.5×)** |
| `Σ_baxis` | `≈ p/2`  | `3.8e−3` (4.8×) | **`2.8e−3` (3.6×)** |
| bulk (`Σ_cpos/cneg`) | `≈ p²/4` | `2.2e−5` (0.03×) | **`4.5e−5` (0.06×)** |

**Reading.** The bulk (hence any bulk-vs-locus contrast, S-C2, and the isotropy χ² whenever the
concentration involves the bulk) is detectable at `≲0.06× δ_global` pooled — very high power. The
**thin strata (axes, diagonal) are power-limited:** pooled, we resolve concentration only if a
thin locus carries `≳2.5–3.6× δ_global` (i.e. `≳3.5–4.6×` the uniform per-cell excess). Per-prime,
only `p ≳ 4000` gives `z=3` sensitivity to a `~5×` thin-locus enrichment. **A null on a thin
stratum therefore BOUNDS its enrichment to `≲2.5×` pooled — it is NOT "no structure" there.**
Co-occurrence arms (S-Cpair, S-mu6): power is plant-calibrated (P3, P4 set to `+5 sd` vs MC-GR);
the run reports the smallest twist-alignment fraction giving pooled `Z=5`. τ-robustness: the same
table at `τ=0.05` (`f=0.0025`, ~4× coarser thin-strata floor) and `τ=0.15` (`f=0.0222`, ~2.2×
finer) — the powered τ for thin strata is `0.15`, for co-occurrence is `0.05` (rarer ⇒ cleaner
alignment signal); reported per τ.

---

## 9. TWO-WAY DECISION RULE + PRE-COMMITTED OUTCOME TABLE (filled before the run)

**A verdict requires τ-robustness (concordant across `{0.05,0.10,0.15}`), NC-floor at floor, the
relevant plant fired, and NC-√N showing `z(n)` rising with `n`.** No row licenses a closure of
N7 or any ECDLP/extraction/security statement, nor the words "generic / benign / tautological /
at the floor / no structure".

| # | Outcome | Conclusion reported |
|---|---|---|
| **A1** | X² permutation p `< 1/(R+1)` at ≥2 of 3 τ AND one `\|z_s\|` dominates, reproducing across τ and with `z(n) ∝ √N` | **Sharpened law:** the near-zero excess CONCENTRATES in stratum `s` (name it: diag / c-axis / b-axis / c-sign half). Report `z_s`, the excess-density there, power + scope. Next probe = the phase structure inside `s`. |
| **A2** | S-C2 fires (`\|z_{D_c}\|>5` pooled, τ-robust, √N-rising) | **c-sign LOCATION asymmetry** named: the excess is not `c↦−c` symmetric. Report the signed half and its density; next probe = the odd-in-c harmonic. |
| **A3** | S-Cpair fires vs **MC-GR** (τ-robust, √N-rising, NC-floor clean) | **c-μ₂ ORGANIZATION** (near-zeros co-occur across `c↦−c` beyond marginal): report the pair-correlation and the imaginary-vs-real decomposition as the next probe. |
| **A4** | S-mu6 fires vs the within-(orbit,sign) null (μ₃-`b` partialled out) | **joint (b,c) μ₆ twist organization** named — the c-coupling the b-μ₃ (ADD3-B) missed. Report `T_μ6`, the twist fraction, power; next probe = the μ₆ isotype decomposition. |
| **B**  | X² p `> 0.05` at all τ AND S-C2/S-Cpair/S-mu6 all null, **with NC-√N confirming they are not variance-suppressed** (i.e. the arms are powered, not flat-by-artifact) | **Bounded characterization (valid output):** the near-zero excess is **isotropic** across `c`-μ₂ / `c=±b` / `(b,c)`-μ₆ to the §8 power (thin strata bounded to `≲2.5× δ_global` pooled; bulk to `≲0.06×`). This NARROWS the mechanism to a **global / moment** effect with no locus in the tested geometric organizers. **Next probe (named, not a closure):** higher-order phase invariants; the **imaginary-part isotype** (ADD3-C's explicitly-open object, untouched by this magnitude-locus drill); a cumulant identity on the near-zero tail. N7 remains live and mechanism-open. |
| **HALT-1** | NC-floor fires (null-vs-null X² inflated, or any arm's null-vs-null `z` outside `N(0,1)`) | Statistic miscalibrated → that arm void, report the miscalibration, no verdict (do not read the real number). |
| **HALT-2** | P1–P4 relevant plant fails to fire, or **P5 trips X²** | "planted control did not fire / rate-leak" → arm void, null uninformative. |
| **HALT-3** | E1 (Parseval) or E-β fails at any prime | bug, not a finding — halt and fix the exact-arithmetic / `(λ,β)` path (as at `p=433/577` in the prior run). |

**Effect-in-an-unprojected-subspace clause (mandatory).** If branch **B**, the run must NOT say
"no structure". It must report (i) the bounded per-stratum enrichment with §8 power + §7 scope;
(ii) an explicit list of what was NOT projected onto — the **imaginary-part isotype**, higher-order
(≥3rd) phase invariants, non-`(b,c)` bases, `a ≠ a₀` outside the forced `⟨λ,−1⟩` orbit,
`p > 12043`; (iii) that a magnitude-locus null licenses none of the phase-space objects.

---

## 10. EXACTNESS

- **Exact `int` / `Fraction`:** curve arithmetic (`x_d,y_d`), the `(b,c)` grid and folding,
  `σ̂²` (Fraction), all stratum memberships and near-zero **counts** `K_s, Q_c, T_μ6`, all
  permutation/rank counts and p-values, the E1 integer Parseval check, the E-β integer assertion,
  the disjointness/cover assertion (§3).
- **Float carve-out (analytic size only, no key in path):** the `p×p` FFT producing `|U|` (the
  sanctioned unit-modulus roots-of-unity magnitude), the reported `z` values. Justification:
  magnitudes of an analytic sum, not key-derived low bits.
- **No verdict decided by float.** `r<τ` is applied to float `|U|` but only the **rank** of the
  resulting integer count against the null decides (Arms X², S-*), and the L2 identity is an
  integer check. `check_no_float.sh` must pass on the counting/partition module before any arm runs.

---

## 11. SELF-AUDIT (mandatory, CLAUDE.md §2a) — mechanical vs frame, uncovered sections named

**(a) Partition / double-counting of the excluded μ₃-`b` [MECHANICAL — discharged].** The primary
partition `P` is a proven disjoint cover of `F\{DC}` (§3, with a run-time assertion); it does not
stratify by μ₃-`b` at all. The μ₆ secondary (S-mu6) partials the μ₃-`b` marginal out by construction
(within-(orbit,sign) permutation holds the b-μ₃ count fixed), so ADD3-B is neither re-litigated nor
double-counted. Discharged with the artifact (the assertion print).

**(b) Variance-artifact risk & null neutralization [MECHANICAL for the guard; FRAME for null
adequacy].** Mechanical: every variance is empirical (MC-H / MC-GR), NC-floor must sit at floor,
and NC-√N voids any arm whose `z(n)` is flat in `n` — the three together are exactly the ADD3-C
correction, and the plant (P3/P4 vs MC-GR) plus the negative NC-floor can expose a
miscalibration. FRAME (NOT self-dischargeable): whether MC-GR truly "preserves every structure
except the one tested" for the μ₆ twist — i.e. whether holding the per-(orbit,sign) marginal is
the RIGHT conditioning, or whether it also destroys a legitimate part of the c-coupling signal —
is a matched-control-adequacy judgment that context-isolation (the experiment-designer gate) is
the mechanism for. **Flagged as owed to that gate; not self-cleared.**

**(c) τ-dependence [MECHANICAL — discharged by design].** All arms run at `τ∈{0.05,0.10,0.15}`;
a verdict requires τ-concordance; a one-τ signal is declared a threshold-boundary artifact. §8
states which τ is the powered one per arm (thin strata: 0.15; co-occurrence: 0.05).

**Uncovered sections, named explicitly (absence from this list is not clearance):**
- **[FRAME] MC-GR conditioning adequacy for S-mu6** — see (b); owed to the isolation gate.
- **[FRAME] organizer non-orthogonality** — axes/diagonal/μ₆/μ₃-`b` overlap; results are reported
  separately with NO joint-independence claim. Whether a concentration attributed to `Σ_diag`
  could be a projection of a μ₆-twist effect (or vice versa) is a frame call the run cannot settle
  internally; the run reports all arms and the overlap counts, and defers attribution.
- **[FRAME] object coverage] this is a MAGNITUDE-locus drill on `|U|`.** It does NOT cover the
  **imaginary-part isotype**, higher-order phase invariants, or any phase-space object (ADD3-C's
  open list). Branch B explicitly routes there and does not close them.
- **[SCOPE] `p = 2²⁵⁶…` and `a ≠ a₀`** (outside the forced `⟨λ,−1⟩` orbit) — out of scope, never
  claimed.
- **[MECHANICAL, run-time] correlation-inflation `ρ`** — the §8 floors assume `ρ≈1`; the run must
  measure `ρ` from the ensemble and re-state every power number with it. If `ρ` on a thin stratum
  is large, that stratum's null may be widened and its bound loosened — reported, not hidden.

**Output type, pre-committed:** a characterization plus bounds, each carrying its §8 power and §7
scope. Never a verdict about ECDLP, extraction, or security; never a closure of N7.
