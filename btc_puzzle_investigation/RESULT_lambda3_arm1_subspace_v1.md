# RESULT — Arm 1+2 of the λ₃ drill: the slow eigenspace has NO covariant excess; it is ⅔ (dimension fraction), FIELD/lattice

**Date:** 2026-07-21 · **Pre-registration:** `PREREG_lambda3_eigenvector_isotype_v1.md` (Arms 1–2, on
the Arm-0-redefined object) · **Script:** `arm1_subspace_lambda3_v1.py` (no-float guard `OK`) ·
**Predecessor:** `RESULT_lambda3_arm0_gate_v1.md` (individual v₃ is GAUGE) · **Deviations:**
`PREREG_lambda3_eigenvector_isotype_v1_DEVIATIONS.md` (D8–D10 added).

**Anomaly-Drill output** (`feedback_anomaly_drill_protocol_2026_07_17`): a characterization + bounded
magnitudes with power and scope; a within-null magnitude is a *size*, not "no structure," and it names
where the (trivial) structure lives.

> ## ⚠ SCALE BANNER
> All numbers at **p ∈ [2503, 3343]**, n∈[2557,3391], K=4. secp p≈2²⁵⁶ — **≥ 239 binary orders above**.
> Zero power at secp. Scoped to `y²=x³+7`, `p≡1 mod 3`, `#E` prime, first-gen orbit, this walk operator.

---

## The object (redefined by Arm 0) and the gauge-free machinery

Arm 0 showed **the individual λ₃ vector is gauge** (near-degenerate cluster). The pre-committed
redefinition: characterize the **slow eigenSPACE's total covariant weight**. Key identity making this
exact and gauge-free (independently re-derived; matches PREREG §0 for m=1):

`W_cov(V) = ⅔ − (1/3m)·tr((UᴴDU)⁻¹ Uᴴ(N₁+N₂)U)`,  V=span(U), dim m,

with **exact integer, walk-independent** matrices over the support S: `N_k[c,c']=#{x∈S: cell(x)=c,
cell(β^k x)=c'}`, `D=diag(#{x: cell(x)=c})`. This is **invariant under any basis U→UR** (a trace) — it
needs only the subspace, not the gauge individual vectors. The **walk** enters only through *which*
span (M's slow eigenspace) is tested against this static μ₃-covariant geometry.

**Machinery validated `[VERIFIED]`:** R1 split identity `2·Σ_S = FIELD+CURVE+(χ₂=0 ledger)` exact to
the integer (6/6 primes); firing FIRES — a known-covariant span → `W_cov=1.000`, known-invariant span
→ `0.143`; and **`w_cov(stationary) = 0.000` exactly** (6/6) — the Perron/cell-marginal vector is
*purely* μ₃-invariant (the x-support is β-symmetric).

## What Arm 1+2 found — `[VERIFIED, scoped p≤3343, K=4]`

**1. The gauge "0.85" is NOT reproduced gauge-free.** On the only stably-defined slow-space object —
the **full non-Perron space** (m=15, `S_sub=1.000` exactly, it is the complement of the stable
stationary vector) — `W_cov ≈ 0.667 ± 0.005` across 6 primes. That is **⅔**, the trivial covariant
dimension fraction — **not 0.85**. The slowest few modes (m=1..5) show variable W_cov (0.53–0.78) but
their spans are **gauge-unstable** (`S_sub = 0.005–0.80 < 0.9`) — not interpretable. **No gauge-free
"slower ⇒ more covariant" gradient exists**; the v25 0.48→0.85 gradient was gauge.

**2. The one reproducible "excess" was a NULL-MISMATCH PHANTOM — killed by the matched null.** The
first-pass null (unrestricted random subspace) flagged `W_cov(m=15)=0.668 > 0.638` "excess" at **6/6**
primes. But that null includes the stationary π-direction that the non-Perron object **excludes**;
since `w_cov(π)=0`, removing one pure-invariant vector rescales `W_cov(non-Perron)=(16/15)·W_cov(full)
=(16/15)·0.625=0.667` — arithmetic, not structure. With a **π-orthogonal matched null** (random
subspaces that also exclude π), the excess **vanishes at every m** (m=8: 0.663 vs null 0.672; m=12:
0.654 vs 0.667; m=15: identical). If anything the slow modes are *marginally below* the matched null.
**No covariant excess at any m.** (This is the `feedback_test_on_both_sets` / v17 control-row lesson:
the null must carry the object's own symmetry, or a 6/6 phantom appears.)

**3. FIELD/lattice, not CURVE/Weil `[VERIFIED]`.** `f_FIELD ≈ W_cov` at every (p,m) — differences
`< 0.02`, both ≈⅔. Removing the χ₂(x³+7) twist changes nothing ⇒ the (trivial) covariant content is
**pure lattice, zero Weil/curve signature**. Hypothesis **H_FIELD confirmed, H_CURVE rejected**
(PREREG Arm 1).

## Characterization (the output)

**The v25/v27 anomaly "λ₃ eigenvector is 85% μ₃-covariant, broadband, no closed form" fully
dissolves.** Gauge-free and matched-null:
- the individual vector is gauge (Arm 0);
- the well-defined slow-space covariant weight is **⅔ — the covariant dimension fraction** — with
  **no excess** over a matched null;
- the only exact structural fact is `w_cov(stationary)=0` (the μ₃-symmetric cell-marginal), a lattice/
  occupancy fact that produces the (16/15) rescaling artifact, nothing more;
- and it is **FIELD/lattice, not Weil**.

This is consistent with the **Cap-Law inert-lens** (θ-independent cell geometry) and with σ being
μ₃-invariant `[PROVED]`: the μ₃ structure of the cell readout is lattice geometry, and M's slow
dynamics do **not** concentrate on it beyond the dimension fraction.

## Grades / retraction

- **RETRACTED `[was EMPIRICAL → GAUGE / null-mismatch]`:** v25/v27's "λ₃ is 60→85% μ₃-covariant" as a
  covariant-*excess* claim. Gauge-free: no excess; W_cov≈⅔. (Arm 0 already retracted the individual
  vector as gauge; Arm 1 adds that even the *subspace* shows no excess, and the one apparent excess was
  a null mismatch.)
- **`[VERIFIED, p≤3343]`:** W_cov(non-Perron)≈⅔ (6/6); `w_cov(π)=0` exact (6/6); f_FIELD≈W_cov (H_FIELD);
  matched-null no-excess; R1 identity exact; firing fires.
- **`[PROVED, re-derived]`:** the gauge-free `W_cov(V)=⅔−(1/3m)tr((UᴴDU)⁻¹Uᴴ(N₁+N₂)U)` (basis-invariant).

## What this does NOT say (drill rule / scale banner)

Not a leak — this is a characterization drill; the slow-space covariance carries no covariant excess
and is a lattice readout of x (floor-bounded, Part V/VI). Not "no structure" — the structure is the
μ₃-invariant stationary/marginal (`w_cov(π)=0`) and the ⅔ dimension fraction, both **named**. Not
"closed" — it is a bounded magnitude (W_cov at the matched-null level, ±0.005, 6 primes, this scale).
Nothing at 2²⁵⁶ (this is 2¹²). The small-m (slowest) modes remain gauge-unresolved at accessible n
(Arm 0 power caveat) — so "no gradient" is scoped to "no gradient in the stably-defined range."

## Bearing on the frontier

The **λ₃-eigenvector anomaly** (v26/v27 "open, no closed form") is **resolved-as-gauge/trivial**: there
is no isolated λ₃ (Arm 0), and the slow-space covariance is the ⅔ dimension fraction with no excess,
FIELD/lattice (Arm 1+2). This item should move from "OPEN lead" to "resolved: gauge + trivial
dimension fraction, no covariant excess, FIELD" in the master — **promotion pending `compile-diff`**
(CLAUDE.md §2). No new leverage toward the gate; the μ₃ covariance is lattice geometry, as Cap-Law
already implied.

## Next probes (if pursued)

The drill ends in a sharper law, not a closure. Live continuations, each its own prereg: (i) push the
small-m (slowest-mode) resolution by extending to prime-order p→10⁵ (would need n~10⁵–10⁶ per the Arm-0
scaling to resolve an individual slow vector — likely inconclusive within scope); (ii) the **other two
hunts** (ε carry-trajectory; ≥3-key/amicable joint-SET) are untouched by this and are where open
surface remains.
