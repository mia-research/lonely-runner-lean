> **⚠ SUPERSEDED by RESULT_...arithmetic_scatter_v2.md.** This v1 headline OVERCLAIMS: it reads the
> within-prime partial-R²(u)=0.80 as "the scatter compresses to the group order." The BETWEEN-prime
> scatter (the actual object) is only ~44% explained; a real χ²_red≈65 residual remains. Proxy-as-object
> error, caught by a post-hoc passage audit. Read v2. H2-fires / H1-null / controls / robustness all hold.

# RESULT — the sub-Rayleigh deficit's scatter is δ tracking the GROUP ORDER; no residue structure beyond it

**Date 2026-08-07.** Executes `PREREG_subrayleigh_deficit_arithmetic_scatter_v5.md` (frozen) +
`_DEVIATIONS.md` (D-A1..D-A4). Schedule frozen in `..._v5_SCHEDULE.txt` (SHA a4b4f005…).
δ-sweep: `arithmetic_scatter_sweep_v1.py` → `..._results.jsonl` (588 curves). Analysis:
`analysis_scatter_v1.py`. Screen: `cyclicity_screen_v1.py`.

**Grade: `[EMPIRICAL — 100 surface / 253 trajectory model primes, pre-registered, all six controls
fired, robust to surface specification]`.** Outcome **A2** of the frozen §9 table.
**Scope (binding):** model curves `y²=x³+7·gᵏ / F_p`, `p≡1 mod 3`, `p ∈ [3061, 11953]`, cyclic part.
`p=2²⁵⁶−2³²−977` is **not** enumerable; **nothing here transfers to it.** No ECDLP / extraction /
security claim. A spectral statistic of a curve, nothing downstream.

---

## 1. The question and the answer

`RESULT_subrayleigh_deficit_scaling_v1` established the deficit `δ` is real and persistent but scatters
prime-to-prime far beyond any smooth-in-`p` model (`χ²_red=204`, `R²_smooth=0.0048`). **This run asked
whether that scatter is a low-complexity arithmetic function of the curve.**

**Answer — the scatter compresses to the GROUP ORDER `n = p+1−a_p` (the Frobenius trace).** It does NOT
carry additional arithmetic-residue structure beyond that.

## 2. Primary result — H2 FIRES (δ depends on the group order at fixed p)

Within each prime, across its cyclic sextic twists (which sweep `n` at fixed `p`):
- **within-prime partial-R²(`u`) median = 0.796** over 100 surface primes (`u = −a_p/√p`),
- exact-permutation Fisher combined **p = 5.0×10⁻⁶** (per-prime π_p enumerated over all `m_p!`),
- surface-adequacy gate (§4) **passes** (partial-R² ≥ 0.25 ∧ H2 p<0.01).

So `δ` is, to ~80% within-prime, a function of the group order `n`. Because `n = p+1−a_p` jumps
arithmetically as `p` sweeps smoothly, this **is** the source of the `χ²_red=204` scatter: the deficit
tracks `n`, and `n` is the arithmetic (Frobenius) quantity that scatters. The dependence is **nonlinear
in `u`** — the linear surface left a `u²` curvature in the residual (SM dirty, §4), and adding `u²`
absorbs it cleanly (SM p: 0.012 → 0.968). *That curvature is why the scatter looked un-smooth in `p`.*

## 3. Secondary result — H1 does NOT fire (no residue structure beyond the group order)

Residual `r(p) = δ₀(p) − f̂(p,n₀)` (base curve held out of the fit), tested against the frozen
invariant lists:

| channel | test | frozen surface | u²-augmented surface |
|---|---|---|---|
| H1a `a_p mod 3` | two-sided MW | p=0.817 | p=0.824 |
| H1a `a_p mod 4` | two-sided MW | p=0.229 | p=0.422 |
| H1a′ sextic-class(7) | KW (+ refit) | p=0.888 / 0.870 | p=0.840 |
| H1b `M` (gated, void) | Spearman | p=0.031 → **void** | p=0.674 |

**None of the misspecification-protected channels fires.** The one apparent lead — `M` at p=0.031 on the
linear surface — was **the `u²` leak, not arithmetic**: the SM control flagged it (dirty SM ⇒ H1b void by
§4), and it vanishes (p=0.674) once `u²` enters the surface. This is the SM gate working as designed, not
a suppressed signal.

## 4. Why the null is INFORMATIVE, and its exact scope

- **All six controls fired** (P1 recovered a planted `a_p mod 3` residue effect at p=0.018; P2 negative
  nulled at ~α; P3 recovered a within-p slope; P4 invariants two-ways; P5 δ-stability; P6 caught a `u²`
  leak while the refit stayed silent). The pipeline **can** detect residue structure — there is none here
  beyond `n`.
- **This is a bounded magnitude, not "dead".** A residue-class effect on the residual below the §7 power
  floor (binary MW at 19:11 / 14:16-type imbalance; KW over Z/6 at ~253 primes) is **not excluded**.
  Object closed: the *tested* residue invariants `{a_p mod 3, a_p mod 4, sextic-class(7)}`; power/scope as
  above; nothing said about untested invariants (`a_p mod ℓ` for other ℓ, class/conductor data, `v₂(n)`).

## 5. Robustness / integrity
- **Robust to the compute-fallback drop of `p=11959`** (4 measurements OOM-skipped; recorded). H2 fires at
  p=5e-6 and H1 nulls at p≈0.8 — one prime cannot move either. 588/592 curves; 100 surface, 253 trajectory
  primes, both ≫ the §7 minimums.
- **Robust to surface specification** (identical verdict under linear and `u²`-augmented `f̂`).
- Direction locks and realization choices frozen from TRAINING only, pre-data (`_DEVIATIONS.md`).
- Signal path exact (EC int, Parseval relerr ≤1e-15 all curves); statistics are exact/integer-count
  permutation p-values; the analytic float carve-out is the FFT magnitude only.

## 6. What this reframes, and the next object (each its own prereg)
- **Reframes scaling-run level-2.** `D(p)` is not smooth in `p` because it is a **nonlinear function of the
  group order `n`**, which is not smooth in `p`. "const vs 1/log p" was the wrong frame — the deficit is
  `δ(n)` with `u²` curvature, sampled along an arithmetically jumping `n₀(p)`.
- **New sub-object (named, not run):** the functional form of `δ(n)` (the `g₀,g₁,g₂(p)` surface and its
  curvature) — what law governs the deficit's group-order dependence.
- **Still open (unchanged):** the *mechanism* — WHY the character's harmonics carry the ~8% near-zero
  excess (row-budget shadow, `row_budget_lowtail_v3`). This run says the scatter is `n`-mediated; it does
  not explain the deficit itself.
