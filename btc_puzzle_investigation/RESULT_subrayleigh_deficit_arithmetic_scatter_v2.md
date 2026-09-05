# RESULT v2 — the group order explains ~44% of the deficit scatter; a real residual scatter remains, and it is NOT the tested residue invariants

**Date 2026-08-07.** Supersedes v1 after a passage audit (triggered by a self-cert word in the v1
writeup) found a **proxy-as-object overclaim**: v1 read the within-prime partial-R²(u)=0.80 as "the
scatter compresses to the group order." The **between-prime** scatter — the actual object — is only
~44% explained. Corrected below. Everything else in v1 (H2 firing, H1 null, controls, robustness) holds.

Executes `PREREG_subrayleigh_deficit_arithmetic_scatter_v5.md` (frozen) + `_DEVIATIONS.md`. Schedule
`..._v5_SCHEDULE.txt` (SHA a4b4f005…). δ-sweep `arithmetic_scatter_sweep_v1.py` → `..._results.jsonl`
(588 curves). Analysis `analysis_scatter_v1.py`.

**Grade: `[EMPIRICAL — 100 surface / 253 trajectory model primes, pre-registered, all six controls
fired, robust to surface spec]`.** §9 cell **A2** (H1 null, H2 fires) — with its conclusion text
corrected to match the measured between-prime fit.
**Scope (binding):** `y²=x³+7·gᵏ / F_p`, `p≡1 mod 3`, `p ∈ [3061, 11953]`, cyclic part. `p=2²⁵⁶−…` is
not enumerable; nothing transfers to it. No ECDLP / extraction / security claim.

---

## 1. What is established, quantified against the RIGHT object

`RESULT_subrayleigh_deficit_scaling_v1` left the deficit's prime-to-prime scatter unfit by any smooth
model (`χ²_red=204`). Three numbers now split that scatter:

| quantity | value | meaning |
|---|---|---|
| **H2** within-prime partial-R²(u), Fisher p | **0.80**, p=5×10⁻⁶ (100 primes) | at fixed p, δ tracks the group order `n` across twists — **strong, real** |
| surface R² on the **between-prime trajectory** | **0.44** (0.42 with u²) | the group order accounts for **~44%** of the actual scatter — **not** "compresses to n" |
| residual scatter after the surface | **χ²_red ≈ 65** (65× SE_δ) | **~56% of the scatter remains, real (65× noise), unexplained by `n`** |

**So the corrected finding, in one line:** the deficit depends on the group order `n = p+1−a_p` (the
Frobenius trace) — that dependence is genuine and is ~44% of the between-prime scatter — but the
majority of the scatter is **not** the group order.

## 2. The residual scatter is NOT the tested residue invariants (H1 null), but it IS real

On the ~56% residual (`r = δ₀ − f̂`), the frozen invariant tests are all null:

| channel | linear f̂ | u²-aug f̂ |
|---|---|---|
| H1a `a_p mod 3` (two-sided MW) | 0.817 | 0.824 |
| H1a `a_p mod 4` | 0.229 | 0.422 |
| H1a′ sextic-class(7) (KW+refit) | 0.888/0.870 | 0.840 |
| H1b `M` (gated; void on dirty SM) | 0.031 → **void** | 0.674 |

`M`'s apparent 0.031 was the `u²` surface-misspecification leak (SM dirty on linear, clean on u²); it
vanishes to 0.674 once `u²` is in the surface — the SM gate working as designed. **No
misspecification-protected channel fires.**

**This is the load-bearing correction to the framing:** a χ²_red≈65 residual is a *real, unexplained*
scatter (65× measurement noise), not a null. H1 says only that it is **not** carried by `{a_p mod 3,
a_p mod 4, sextic-class(7)}` at this scope/power. It is a **live open object**, not a closure.

## 3. Why the null part is informative, and its exact scope
- **All six controls fired** (P1 recovered a planted `a_p mod 3` effect at p=0.018; P2 nulled at ~α; P3
  recovered a within-p slope; P4 invariants two-ways; P5 δ-stability; P6 caught a `u²` leak while the
  refit stayed silent). The pipeline can see residue structure; there is none in the residual beyond `n`.
- **Object bounded:** the *tested* invariants `{a_p mod 3, a_p mod 4, sextic-class(7)}`; power per §7
  (binary MW at ~19:11 imbalance; KW over Z/6 at 253 primes). Untested and still open: `a_p mod ℓ` for
  other ℓ, class/conductor data, `v₂(n)`, and the functional law of the χ²_red≈65 residual itself.

## 4. The prereg gap this audit exposed (record it)
§9-A2 was worded "H2 fires ⇒ the scatter is δ's dependence on group order n." That step is a
**proxy-as-object leap**: H2 fires is a *within-prime* statement; whether the surface explains the
*between-prime* scatter is a separate measurement (the trajectory R², 0.44) that §9 never required.
A future prereg of this shape must gate the "explains the scatter" conclusion on the between-object R²,
not on the within-object partial-R². (This is the same within-vs-between confusion the v2→v3 obstruction
warned about, recurring at the reporting layer.)

## 5. Robustness / integrity
- Robust to the compute-fallback drop of `p=11959` (4 OOM-skipped curves; recorded): H2 p=5e-6, H1
  p≈0.8, trajectory R² 0.44 — one prime moves none of these. 100 surface, 253 trajectory primes ≫ §7 mins.
- Robust to surface spec (linear vs u²-augmented: trajectory R² 0.44 vs 0.42; H1 null in both).
- Direction locks / realization choices frozen from TRAINING only, pre-data.
- Signal path exact (Parseval relerr ≤1e-15 all curves); permutation p-values integer-count; float
  carve-out = FFT magnitude only.

## 6. Next objects (each its own prereg)
- **The χ²_red≈65 residual** — the majority of the scatter, real, not the tested residues. What carries
  it? (finer arithmetic; or a genuinely un-compressible per-curve quantity). This is the live lead.
- **The functional law `δ(n)`** — the surface's `g₀,g₁,g₂(p)` and curvature.
- **Mechanism (unchanged, still open):** WHY the ~8% near-zero harmonic excess exists (row-budget thread).
