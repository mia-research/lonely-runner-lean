# RESULT — Arm 0 (GATE) of the λ₃ eigenvector drill: the individual λ₃ vector is GAUGE

**Date:** 2026-07-21 · **Pre-registration:** `PREREG_lambda3_eigenvector_isotype_v1.md` (Arm 0) ·
**Script:** `arm0_gate_lambda3_v1.py` (no-float guard: `OK`) · **Deviations:**
`PREREG_lambda3_eigenvector_isotype_v1_DEVIATIONS.md`.

**Anomaly-Drill output** (`feedback_anomaly_drill_protocol_2026_07_17`): a characterization + bounded
magnitudes with power and scope. Not a verdict, not a closure. Dissolution into a sharper law is
positive.

> ## ⚠ SCALE BANNER
> All numbers at **p ∈ [2503, 3571]**, n ∈ [2557, 3469], K=4 (K-sweep 4–10 at the top prime). secp is
> p≈2²⁵⁶ — **≥ 239 binary orders above**. Zero power at secp. Scoped to `y²=x³+7`, `p≡1 mod 3`,
> `#E` prime, first-generator orbit, this walk operator M.

---

## The question (well-definedness only — no hypothesis tested)

Is "**the** λ₃ eigenvector" of the d→d+1 cell-walk transfer operator `M` (16 states at K=4) a
well-defined object, or gauge? v25/v27 reported it "60→85% μ₃-covariant, broadband, no closed form,
open." The gate decides whether that individual vector even exists as a canonical object before any
covariance is attributed.

## What was run

- **Firing calibration (mandatory control).** Two synthetic plants through the identical pipeline: a
  well-separated chain SEP (analytic |λ₂|=0.920, |λ₃|=0.767, gap **0.153**) and an exactly-degenerate
  tensor chain DEGEN (analytic |λ₂|=|λ₃|=0.773, gap **4.4e-16**). Swept over n. **Result:** the gate
  resolves SEP's well-defined vector to half-orbit stability `S>0.9` at **n*≈2500**, and simultaneously
  reads DEGEN as `S_sub≫S` (2-dim slow subspace stable, individual vector gauge). The gate machinery
  works and its power threshold for a gap≈0.15 is n≈2500.
- **Powered set.** 8 prime-order curves with n ≥ n*=2500 (pre-committed power-budget extension):
  p = 2503, 2647, 2677, 2731, 3271, 3343, 3511, 3571. (The 12 smallest committed primes, n∈[397,1303],
  are all **below n\*** — underpowered, reported but not decisive; see Deviations.)

## What the gate found — `[VERIFIED, scoped p≤3571]`

**1. There is no isolated λ₃: the subdominant spectrum is a dense near-degenerate cluster.**
After a large Perron drop (λ₁=1 → |λ₂|≈0.11–0.15), the subdominant |λ| pack into a narrow band with
pairwise gaps **0.0005–0.024, every one within the 3σ bootstrap noise (≈0.04–0.05)**:

| p | \|λ₂..λ₈\| |
|---|---|
| 2503 | 0.1496 0.1258 0.1170 0.1064 0.0935 0.0844 0.0765 |
| 3343 | **0.1115 0.1110** 0.0926 0.0876 0.0691 0.0600 0.0531 |
| 3571 | 0.1326 0.1112 0.1085 0.0973 0.0804 0.0649 0.0617 |

`Δ₂₃ < 3σ₂₃` at **8/8** powered primes. `Im λ₃ = 0` everywhere (real band, not a conjugate pair).

**2. The individual λ₃ vector is unstable across half-orbits — and so is the 2-dim {v₂,v₃} pair.**
`S(v₃) = 0.002–0.571`, all `< 0.9`. `S_sub(v₂,v₃) = 0.30–0.78`, also `< 0.9` — the subdominant cluster
is **more than 2-dimensional**, so even the pair-subspace bleeds into λ₄,λ₅,… . Firing proves this is
not generic underpower: at the same n, SEP's genuinely well-defined vector reached `S>0.9`.

**3. Power caveat, stated (drill rules 2–3).** n*=2500 was calibrated for SEP's gap **0.15**. The real
subdominant gaps are **~0.02** (≈7× smaller); individual-eigenvector resolution scales like
`n ∝ 1/gap²`, so resolving a real individual vector would need **n ~ (0.15/0.02)²·2500 ≈ 10⁵–10⁶** — at
or beyond the accessible prime-order range. So the individual vector is **not resolvable at accessible
scale**; the band is *near-degenerate/unresolved*, which is neither "proven exactly degenerate" nor
"well-defined."

**4. The covariant weight is additionally K-dependent** (corroborating, at p=3571):
w_cov(K=4,6,8,10) = **0.862, 0.729, 0.701, 0.651** — drifts down 0.21 across K (slowing:
|w(10)−w(8)|=0.049 < |w(6)−w(4)|=0.134). The K=4 value "0.85" is inflated relative to finer cells even
before the gauge problem. (This w_cov is itself computed on the gauge v₃, so its drift is partly the
gauge instability — reported as color, not an independent invariant.)

## Characterization (the output)

**The anomaly "λ₃ eigenvector is 85% μ₃-covariant, no closed form" DISSOLVES into a sharper statement:
there is no canonical λ₃ eigenvector.** M is strongly mixing (|λ₂|≈0.13) with a dense near-degenerate
subdominant band; the "λ₃ eigenvector" returned by `np.linalg.eig` is one arbitrary representative of a
rotation-equivalence class within that band. This **explains** v27's "no simple closed form": a
non-canonical vector in a near-degenerate cluster cannot have one.

**This is consistent with the PROVED tensor structure.** The addition-law operator `C_T = C₁⊗C₁` has
`λ₂=λ₃=1/3` **exactly** degenerate (master §X.10). The empirical d→d+1 walk operator M is a different
construction but exhibits the same qualitative feature — a near-degenerate slow band — so its
individual subdominant eigenvectors are gauge for the same reason.

## Grades and the retraction

- **RETRACTED as an individual-eigenvector statement** `[was EMPIRICAL, now GAUGE]`: v25's
  `λ₃ covariant w₁+w₂ = 0.60→0.85` and `λ₂ ≈ 0.48` split, and v27 #1's "the λ₃ eigenvector is 85%
  μ₃-covariant, broadband." These depend on which representative the eigensolver returns from the
  near-degenerate band, and additionally drift with K. **They are not properties of a well-defined
  object.** (v27 already graded this EMPIRICAL/open and flagged "no closed form" — the gate now names
  *why*: it is gauge.)
- **`[VERIFIED, p≤3571]`** the three measured facts (1)(2) above and the firing calibration.
- **Load-bearing algebra `w_cov = ⅔(1−Re A)`** independently re-derived (PREREG §0); as a byproduct the
  gate reproduces v25's number at p=433 (w_cov=0.596 vs reported 0.60) — the formula and the record's
  measurement agree; it is the *interpretation as an individual-vector invariant* that fails.

## Object redefinition (pre-committed GATE-FAIL branch) — where Arm 1 goes

Per the prereg, a failed gate **redefines the object**, it does not proceed on a gauge quantity. The
well-defined object is **not** any individual vector but the **slow eigenSPACE** (the clustered
subdominant band) and its **TOTAL** covariant weight `W_cov = Σ_{k∈{1,2}}‖P_k Π‖²_F/‖Π‖²_F` (Π the
band projector — basis-independent). **Open sub-task before Arm 1:** the band is >2-dimensional and has
no clean internal gap at accessible n, so the band DIMENSION must be fixed by a rule (a real spectral
gap below the cluster, or a fixed slow-|λ| threshold), and Π's own half-orbit stability `S_sub(Π)`
must be checked — Arm 1 runs only on a Π that is itself stable.

## What this does NOT say (drill rule, scale banner)

Not "the covariance is fake" — the FIELD/CURVE covariant *weight of the stable band* (Arm 1) is the
live question and is untouched here. Not "closed" — the frontier moves from a gauge vector to a
well-defined subspace object. Not any statement at 2²⁵⁶ (this is a 2¹² measurement). Not "exactly
degenerate" — *near*-degenerate/unresolved at accessible n.

## Next probe

Arm 1 on the redefined object: (i) fix the slow-band dimension m by the first real gap below the
cluster (or a slow-|λ| cut), verify `S_sub(Π_m) > 0.9` on the powered set; (ii) compute `W_cov` of Π_m
and its FIELD vs CURVE split (PREREG Arm 1) with the μ₃-preserving matched null (PREREG Arm 2). If no
Π_m is stable at accessible n, Arm 1 abstains with a band + n-needed — scoped, not a closure.
