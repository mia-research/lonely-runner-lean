# RESULT — flap doubling 2×2 is `a`-homogeneous at 4× the prior resolution (v1, 2026-07-23)

**Spec:** `PREREG_flap_a_invariance_v1.md` (frozen before any per-`a` table was computed).
**Deviations:** `PREREG_flap_a_invariance_v1_DEVIATIONS.md` (D1 centred statistic, D2 validation run
exploratory, D3 classifier densities, D4 gate pool, D5 `check_no_float` fails on the carve-out lines,
D6 sweep `B`, D7 arms not run).
**Run:** `flap_a_invariance_v1.py 1000000 9999` → `flap_a_invariance_run_v1.out`.
`a_sample_v1.txt` SHA-256 `fdadbe8c…c908e6`, written **before** the pool existed.

---

## 1. The question

The completed group-law run (`flap_grouplaw_run_v1.out`) tested `(ε(X), ε(x(2P)))` at **one** fixed
classifier multiplier `a` and returned null. `a` was never varied. Motivating principle, imported from
the LRC blocking-grammar work (Coupling Principle, `../lrc_n11_algebraic_lemma_v1.md` Lemma 2.2):
*when one parameter moves, all cells of a piecewise-constant classifier scale together — you cannot
shift one without the others.* If the joint statistic is `a`-invariant, the null is a property of the
`ρ`-lattice rather than a magnitude bound at one arbitrary `a`.

**The question is well posed, and the joint is not forced.** `ε_a(X) = ε_1(aX)`, so varying `a`
relabels which abscissas are flap; but scaling and doubling do not commute, so the joint is
`(ε_1(Y), ε_1(D_a(Y)))` with `D_a = m_a ∘ x2 ∘ m_a⁻¹` a **degree-4** map for every `a` — never a
relabelling. Both margins are pinned for every `a`, leaving exactly **one** free degree of freedom,
the log-odds `θ_a`.

**Effective `a`-space is `(ℤ/p)*/μ₆`, not `(ℤ/p)*`.** `ε(ζY) = ε(Y)` for `ζ ∈ μ₆`, and
`x2(βX) = β·x2(X)` exactly (`β⁴=β`, `β³=1`), hence `D_{βa} = D_a` as maps and the 2×2 for `a` and `ζa`
is cell-by-cell identical. `K = 32` `μ₆`-orbit-distinct values were drawn; **32 is the distinct
configuration count**, and no tally may cite more.

---

## 2. Result — all three statistics null, every control behaved

```
theta_a:  mean = +0.00044   sd = 0.00504   min = -0.00974   max = +0.01309

D_cen (PRIMARY dispersion)   rank = 6363 / 9999   -> null
M_cen (sparse alternative)   rank = 4057 / 9999   -> null
theta-bar (pooled mean)      rank = 6417 / 9999   -> null
```

The observed spread `sd = 0.00504` sits **at the sampling-noise floor**: under `a`-invariance the
expected SD of `θ_a` is `√V = 16/(3√n) = 0.00533`. Observed ≈ expected; there is no excess dispersion
to account for.

**Gates and controls (§4, §3):**

| control | requirement | observed |
|---|---|---|
| G2 `μ₆`-invariance | 0 exceptions | **0 / 131072** |
| G3 quarter-density | all 32 in band | **0 failures**, abs-form mean `0.24957` |
| G5 `x2` vs independent affine doubling | 0 mismatches | **0 / 200** |
| PC-max (`X↦βX` forced diagonal) | must fire | **fires**, 0 off-diagonal cells |
| PC-id (2×2 for `a` vs `βa` identical) | 0 exceptions | **0** |
| PC-dep-arith (8 of 32 forced-diagonal) | must fire | **fires**, rank 0 |
| PC-dep-NEG (`h=K`, common shift) | must **NOT** fire | **null**, rank 4372 ✓ |
| PC-FP (100 pure-null realizations) | ≤ 3/100 | **3/100** |
| PC-dep-α (empirical detection floor) | must be printed with the null | **see §3** |

**PC-dep-NEG is the load-bearing one.** The spec's original `D_int = Σ_a dev_a²` is an *uncentred*
sum of squares, so a shift common to every `a` inflates it — and it duly fired under PC-dep-NEG,
VOIDing itself as a dispersion statistic. That is the control working exactly as designed, catching a
proxy-reported-as-object defect **written into the frozen spec**. Replaced by the centred
`D_cen = K·Σdev² − (Σdev)²` (exact integers), under which PC-dep-NEG correctly stays silent while the
mean statistic `θ̄` remains uncentred. Full account: deviation D1.

---

## 3. PC-dep-α — empirical detection floor (`flap_a_powercal_run_v1.out`)

Independence background + forced agreement on the first `m = ⌊αn⌋` indices for `h` of the `K = 32`
values of `a`; 100 reps per cell; `τ = √((h/K)(1−h/K))·4α`.

| h | α | τ | empirical power of `D_cen` |
|---|---|---|---|
| 8 | `2⁻⁸` | `6.77·10⁻³` | **1.00** |
| 8 | `2⁻⁹` | `3.38·10⁻³` | 0.47 |
| 1 | `2⁻⁷` | `5.44·10⁻³` | **0.98** |
| 1 | `2⁻⁸` | `2.72·10⁻³` | 0.35 |
| **32** | `2⁻³` | `0` (no dispersion) | **0.00** |
| **32** | `2⁻⁴` | `0` (no dispersion) | **0.02** |

**The `h = 32` rows are PC-dep-NEG at full strength**: an identical shift planted in *every* `a`
produces zero dispersion, and `D_cen` stays silent even at `α = 2⁻³` (a `δ = 3α/4 ≈ 9%` shift). The
centred statistic measures heterogeneity, not a common mean shift — the defect that VOIDed the spec's
original `D_int` (D1) is confirmed absent.

**The sweep grid is coarse (factor-2 steps in `α`), so the smallest *firing grid point* overstates the
floor.** Reading the crossings:
- `h = 8`: power `0.47 → 1.00` between `τ = 3.38·10⁻³` and `6.77·10⁻³` ⇒ 0.8-crossing ≈ **`4.7·10⁻³`**;
- `h = 1`: power `0.35 → 0.98` between `τ = 2.72·10⁻³` and `5.44·10⁻³` ⇒ 0.8-crossing ≈ **`4.6·10⁻³`**.

Both land on the analytic `τ_min = 4.7·10⁻³` of spec §5 — **the calibration check the spec asked for
passes.** The sparse arm agrees too: the analytic `M_cen` floor `|θ_a| ≥ 2.3·10⁻²` sits inside the
measured `h = 1` bracket (`θ_plant ≈ 4α`: 0.35 power at `1.6·10⁻²`, 0.98 at `3.1·10⁻²`).

**Two floors are therefore reportable, and both are given below:** the conservative grid floor
`τ = 6.8·10⁻³` (smallest swept `α` reaching power ≥ 0.8 outright) and the interpolated 0.8-crossing
`τ ≈ 4.7·10⁻³` that matches the analytic value.

---

## 4. Pre-committed conclusion (§7 bullet 2, §8 row 2) — a scoped magnitude bound

> Dispersion of `θ_a` across **32** uniform `μ₆`-distinct `a` (bit-length ≥ 200) is bounded by
> **`τ < 4.7·10⁻³`** (log-odds SD; **`8.7·10⁻⁴`** in `P(F|F)` units) — analytic, and confirmed by the
> PC-dep-α 0.8-crossing at `4.6–4.7·10⁻³`; conservatively `τ < 6.8·10⁻³` at the swept grid floor. And
> **no single sampled `a` deviates by `|θ_a| ≥ 2.3·10⁻²`** (measured sparse bracket
> `1.6·10⁻² … 3.1·10⁻²`), at `n = 10⁶` per `a`, power 0.8, `α* = 1/60`, secp256k1, 1-bit `ε`,
> absolute-value classifier form.

**Detection-floor caveat that must travel with this bound:** `D_cen` has **zero power against a
uniform `a`-independent shift** by construction (`h = 32` rows, §3). A coupling that is *identical*
across all `a` is invisible to the dispersion arm — it is the `θ̄` arm that covers that case, and
`θ̄` carries the undischarged shared-pool caveat below.

Secondary: the **universal**-`θ` bound tightens from the prior run's `δ < 3.4·10⁻³` to
**`δ < 5.7·10⁻⁴`** in `P(F|F)` — subject to the shared-pool caveat below.

**The permissible upgrade over the completed single-`a` run is exactly this and nothing wider:**
*the T1 null is not an artifact of the single `a₀`; it holds uniformly over a 32-point sample of the
effective `a`-space, at ~4× finer resolution.*

**Reserved words, per the spec.** This is **not** a proof of rigidity. "The null is forced" and "the
`ρ`-lattice is rigid" require an **analytic** derivation — e.g. that `⟨1_{S₁}, 1_{S₁}∘D_a⟩` is
independent of `a` — and this experiment cannot produce one. So the Coupling-Principle question that
motivated the run is **not** answered; it is bounded. A sample of 32 orbits out of `(p−1)/6 ≈ 2²⁵³`
bounds the **typical** `a`, never every `a`.

---

## 5. Scope — a null here excludes none of these

(i) the full Eisenstein/Dedekind rhombus position, of which `ε` is a **1-bit projection** — an effect
living in the full lattice position would read null through this bit; (ii) `ν_π` / lattice class;
(iii) higher iterates `x(2^k P)`, `k ≥ 2`, and `x(mP)`, `m > 2`; (iv) `≥3`-point joints;
(v) `ε` coupled to `y`; (vi) `a` with bit-length < 200 (excluded by the pre-registered filter, so
`a ∈ {1,2,3}` are untested); (vii) any `a` outside the 32 sampled orbits.

**Two material gaps, disclosed rather than filtered (D7):**
- **Null-I was not run.** The `θ̄` arm therefore carries an **undischarged shared-pool caveat**: all
  32 values of `a` read the *same* pool, so the `θ_a` are not independent and the outcome-table row
  *"Agreement ⇒ the shared-pool coupling is not driving Null-P"* was never tested.
- **The §1.5 stratification and the §6.1 reference panel were not run**, so `θ_a` has not been tested
  against any `μ₆`-invariant of `a`, and the prior run's `a₀` is not placed against the confirmatory
  `θ_a` distribution.

**Not "closed", not "rigid", not "avenue dead."** No ECDLP content: this bounds the dependence between
two flap bits under doubling; it says nothing about recovering `d`.

*Grade legend: PROVED · VERIFIED · EMPIRICAL (scoped, controls fired) · HYPOTHESIS · CITED.*
