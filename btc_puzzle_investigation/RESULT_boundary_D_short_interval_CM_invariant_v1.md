# RESULT — Boundary D executed: the {χ₃, s, GLV-decomp} cross-representation gives NO sub-√(W/6) short-interval lever

**Date:** 2026-08-13. Executes `PREREG_boundary_D_short_interval_CM_invariant_v1.md` (frozen before data);
deviations in `..._DEVIATIONS.md`. **Grade:** `[EMPIRICAL — SCOPED NULL / collapse, both firing controls fired]`.
**Outcome A of the pre-committed table.** A BOUND on this mechanism at this scale — **NOT a closure of the
CM/interval avenue.** Scripts: `bd_foundation.py` (curves + #E BSGS, validated 4/4 vs brute),
`bd_engine.py` (baseline + candidate, self-tests recover d on all 3 curves), `bd_run.py` (grid + FC1 + FC2 + Outcome-D).

---

## 1. The object (per spec §0)

Short-interval DLP: recover secret `d ∈ [0,W)`, `W=2^N ≪ n`, from public `Q=[d]G` on a j=0 CM curve
`y²=x³+b`, using the CM ingredients {`χ₃(x(Q))` cubic-residue label, `s` Eisenstein norm, GLV lattice}.
Cost = group operations (exact integer counter). Bar to beat = **negation-accelerated interval kangaroo**.

**Structural finding that reframes the baseline (sharper than the spec assumed):** for a *short* interval,
the endomorphism φ = mult-by-λ does **not** preserve `[0,W)` — `λ·d` scatters over `[0,n)`. So of the μ₆
automorphisms, only **negation** accelerates interval DLP (√2); the φ/GLV part (hence χ₃, the φ-orbit label)
gives **no interval gain**. This is *why* the CM ingredients collapse here, made mechanical.

## 2. GRID — slope ½, R_optimal = 1 (three scales, M=50)

Curves (prime order, n≡1 mod 3, non-anomalous, large embedding degree): A `p≈2^37`, B `p≈2^41`, C `p≈2^45`.

| scale | N=20 | N=24 | N=28 | slope(log₂ops vs N) |
|---|---|---|---|---|
| A | base 1472 · R_sec 1.35 · R_opt 1.000 | 5638 · 1.39 · 1.000 | 23531 · 1.36 · 1.000 | **0.500** |
| B | 1366 · 1.47 · 1.000 | 5593 · 1.29 · 1.000 | 22410 · 1.38 · 1.000 | **0.505** |
| C | 1342 · 1.54 · 1.000 | 5810 · 1.27 · 1.000 | 24512 · 2.13 · 1.000 | **0.524** |

- **slope ≈ ½ at all three scales** ⇒ baseline cost `~√W`; no sub-√ lever.
- **R_optimal = 1.000 everywhere** ⇒ the optimal candidate ignores the CM ingredients (= baseline).
- **R_sector = 1.3–2.1 > 1** ⇒ the concrete χ₃-sector prune is *strictly counterproductive*: χ₃(x(Q)) is
  only the orbit label (verified `i1_shortinterval_localizer_check.py`: 0 bits about d's position in a
  2^18 secp interval, perm p=0.94), so it cannot predict which sector the answer's baby-step occupies, and
  attempting to exploit it just adds redundant passes.

## 3. OUTCOME-D — no sub-representation structure

Between-χ₃-sector variance of the baseline op-count, exact permutation null (N=24):
A p=0.069, B p=0.571, C p=0.152 — all >0.05. The op-count residual does **not** live in a χ₃ sector split.

## 4. FIRING CONTROLS — both required, both fired

**FC2 (planted top-t-bit leak, curve B, N=24):** revealing `t` high bits shrinks the interval `2^t`;
op-count must drop `2^{-t/2}`.

| t | R_FC2 (measured) | predicted 2^{−t/2} |
|---|---|---|
| 4 | 0.2485 | 0.2500 |
| 8 | 0.0611 | 0.0625 |
| 12 | 0.0168 | 0.0156 |

Near-perfect, monotone — the meter resolves a graded win of known magnitude to <5% relative error.

**FC1 (anomalous curve `y²=x³+x+40172 / 𝔽_{2^30+…}`, #E=p, SSSA → polylog):** SSSA recovers d **12/12**
with a **flat** op-count (69, polylog) while baseline grows `√(2W)`. R_FC1 crosses its pre-committed
`W^{-0.3}` bar and **FIRES**:

| N | SSSA ops | baseline ops | R_FC1 | W^{−0.3} | |
|---|---|---|---|---|---|
| 24 | 69 | 5030 | 0.0137 | 0.0068 | (constant not yet swamped) |
| 28 | 69 | 25758 | 0.00268 | 0.00296 | **FIRES** |
| 29 | 69 | 29013 | 0.00238 | 0.00240 | **FIRES** |

The bigger anomalous curve was used specifically so FC1 meets its own threshold rather than being
reinterpreted post-hoc (`feedback_prereg_abstention_is_the_finding`). **Both firing controls fired.**

## 5. Reading (pre-committed Outcome A)

slope ≈ ½, R_optimal ∈ [0.9,1.1], stable over 3 scales, both firing controls fired ⇒ **SCOPED NULL / collapse.**

- **Object:** short-interval DLP on j=0 CM `y²=x³+b`. **Class of observable:** group-op cost of any
  {χ₃, s, GLV-decomp} cross-representation vs the negation-accelerated kangaroo.
- **Power:** FC2 resolves `2^{-t/2}` graded wins to <5%; detection ceiling `Δ_min ≈ 0.11` (M=50).
- **Scope:** j=0, `n≈2^{37,41,45}`, `N∈{20,24,28}`, M=50, exact arithmetic. **Zero power vs 2^256** — this
  measures the MECHANISM.
- **NOT closed:** the CM/interval avenue at large; non-generic transfers on out-of-scope regimes
  (anomalous, small embedding degree); higher-order joint-set structure (boundary C). A BOUND, not a closure.

**Why it collapses, in one line:** the only automorphism that preserves a short interval is negation (√2);
φ/χ₃/GLV — the CM ingredients — scatter the interval or reduce to the orbit label, so they add nothing a
generic search doesn't already have. Consistent with the single-point closures earlier in this program
([[secp-amicable-transport-circular-2026-08-13]]): the surviving routes are class-(J) joint-set, not
per-point/interval CM readouts.
