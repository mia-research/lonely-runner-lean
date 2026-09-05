# RESULT — `k_den` level sets are exactly the primitive-`j/q` comb (H2b/H2a, v1, 2026-07-23)

**Spec:** `PREREG_kden_ramanujan_comb_v1.md` (frozen before any level set or run count was computed).
**Deviations:** `PREREG_kden_ramanujan_comb_v1_DEVIATIONS.md` (D1 plant fix, D2 H3 not run, D3 `q=1`).
**Run:** `kden_ramanujan_comb_v1.py` → `kden_ramanujan_run_v1.out`. Endpoint hashes:
`kden_endpoint_hashes.txt`. `check_no_float.sh`: **OK** (no float anywhere in this arm).

---

## 1. Headline `[VERIFIED EXACTLY + DERIVABLE]`

For `k_den(off; A, M) = argmin_{1≤den≤M} |den·off − k·A|` (the band best-approximation denominator of
`lift_band_spectral_v1.band_residual`), the level set `L_q = {off ∈ [0,A) : k_den = q}` is **exactly**
the disjoint union of intervals centred on the fractions `j/q` with `gcd(j,q)=1` — of which there are
**`φ(q)`**.

```
POOLED   intervals = 9726    mismatch_interior = 0    mismatch_boundary = 0
POOLED   H2a-safe   314/314 informative safe cells      (r_q = φ(q))
POOLED   H2a-tight  127/127 informative deficiency cells (r_q = r̂_q)
```

Over **675 840 offsets** across **8 out-of-sample `(bexp, M)` configurations**, the predicted
assignment and the computed `k_den` agree at **every single offset** — zero interior mismatches and
zero boundary mismatches. The predicted intervals **tile** each band exactly (`covered = A` in all 8).

**This is "verified, and derivable" — not "discovered."** §0.4 of the spec derives the containment
direction from Dirichlet + a three-distance argument *before* any data: any `off` with `k_den = q`
satisfies `‖qθ‖ ≤ 1/(M+1)`, hence lies within `1/(q(M+1))` of some `j/q`, and a centre with
`gcd(j,q) = g > 1` is beaten by `q/g`. The run confirms the closed-form endpoints exactly and
out-of-sample; it does not establish a previously unknown law.

| id | bexp | A | M | intervals | Σφ(q) | mismatch | safe cells | deficiency cells |
|---|---|---|---|---|---|---|---|---|
| W1 | 17 | 65536 | 31 | 308 | 308 | 0 | 29/29 | 0/0 |
| W2 | 17 | 65536 | 36 | 396 | 396 | 0 | 34/34 | 0/0 |
| W3 | 19 | 262144 | 41 | 530 | 530 | 0 | 39/39 | 0/0 |
| W4 | 19 | 262144 | 60 | 1102 | 1102 | 0 | 58/58 | 0/0 |
| T1 | 12 | 2048 | 43 | 584 | 584 | 0 | 26/26 | 15/15 |
| T2 | 12 | 2048 | 45 | 628 | 628 | 0 | 26/26 | 17/17 |
| T3 | 14 | 8192 | 101 | 3138 | 3144 | 0 | 51/51 | 48/48 |
| T4 | 14 | 8192 | 100 | 3040 | 3044 | 0 | 51/51 | 47/47 |

---

## 2. The deficiency arm is much thinner than `127/127` suggests — stated plainly

`Q_safe = {q : q(q+M) ≤ A}` is the spec's *sufficient* condition for every one of the `φ(q)` intervals
to contain an integer. The 127 "informative deficiency cells" are the cells **outside** `Q_safe`. But
outside `Q_safe` is not the same as deficient, and in fact:

| config | cells where `r̂_q < φ(q)` |
|---|---|
| T1 (A=2048, M=43) | none |
| T2 (A=2048, M=45) | none |
| T3 (A=8192, M=101) | `q=97`: 92 vs `φ=96` · `q=98`: 40 vs `φ=42` |
| T4 (A=8192, M=100) | `q=97`: 92 vs `φ=96` |

**Only 3 cells across 2 configurations actually exercised a deficiency prediction** (10 intervals
predicted empty in total). The remaining 124 cells predicted `r̂_q = φ(q)` — i.e. *no* deficiency
despite lying outside `Q_safe` — and that held. So `Q_safe` is **sufficient, not necessary**, and the
`127/127` figure mostly certifies that the criterion does not over-predict deficiency.

The 3 genuine cells were predicted **exactly** (92, 40, 92 against `φ` of 96, 42, 96), out of sample.
That is a real hit on the non-trivial half of §0.4, and it is a small one. Both statements belong.

---

## 3. Controls

All three wrong-prediction plants fire on all 8 configurations (§4.1 requirement):

| plant | what it asserts | mismatch range over C |
|---|---|---|
| W1 (all `j`, no coprimality) | `q` intervals instead of `φ(q)` | 481 … 63406 |
| W2 (half-shifted centres) | centres at `(2j+1)A/2q` | = `A` (total) on every config |
| W3 (half widths) | right centres, wrong endpoints | ≈ `A/2` on every config |

W3 is the one that makes H2b stronger than H2a: it proves the comparator is sensitive to **endpoint
positions**, not merely to which centres are occupied.

**W1 failed to fire on first implementation and VOIDed the arm until fixed** (deviation D1). The cause
is itself content: at a non-primitive centre some `d` gives `u_d = 0`, collapsing the derived width to
zero, so "intervals at all `j`" silently reproduced the primitive prediction. The coprimality filter
is not imposed on the geometry — it falls out of it.

---

## 4. Scope — every number above is bounded by this

- `bexp ∈ {12, 14, 17, 19}`; `M ∈ {31, 36, 41, 43, 45, 60, 100, 101}`; `A` a power of two.
- **NOT covered:** `M > 101`, non-power-of-two `A`, the regime `A ≫ M²` beyond `bexp = 19`,
  and any `(bexp, M)` outside the 8 listed.
- The three previously-seen configurations (S1–S3: `(11,32), (13,48), (15,64)`) are in-sample and were
  excluded from every tally above.

**Scope correction to the prior result, recorded.** `lift_band_joint_findings_v1.md` Part 2 reported
the low-frequency excess as "growing with curve size" across three curves. `k_den` depends only on
`(off, A, M)` — **no elliptic curve enters its definition**. In that prior run `bexp`, `M`, and the
curve order moved together, so the reported trend was three-way confounded. This is a scope
correction on how that trend may be described; it does not dispute the measured excess values.

---

## 5. What this does and does NOT establish

- **Establishes:** `L_q` is the primitive-`j/q` comb, exactly, at 8 fresh configurations, with the
  count `φ(q)` and the closed-form endpoints of §0.4. `[VERIFIED + derivable]`
- **Does NOT establish anything spectral.** H3 was not run (deviation D2). In particular the
  `|f| = 12/24/24` top modes reported in-sample remain **unexplained by any confirmatory test here**;
  the equal-width Ramanujan factorization (HYP-S) is **untested**; and the pre-committed
  `M = 100` vs `M = 101` cutoff-versus-factorization contrast is **undecided**. Per §0.3 F-1, HYP-S is
  precisely the part that HYP-G does *not* force, so it carries the non-forced spectral content — and
  it is exactly what has not been done.
- **No curve, lift, `derr`, or `d`-side claim.** `k_den` is pure band arithmetic and is a function of
  `d` alone. Nothing here bears on recovering `d`. **No ECDLP content.**

**Next object (unchanged by this run):** execute H3 — build `RAM(f)` and `FLAT(f)` from the now-exact
geometry, hash `TOP3_pred` before computing `P_obs`, run PC-comb / PC-comb-α / PC-neg, and settle the
`M=100` vs `M=101` contrast. That is what would connect this to the `|f|=24` mode that motivated it.

*Grade legend: PROVED · VERIFIED (exact/numeric at scale) · DERIVABLE · EMPIRICAL (scoped, controls
fired) · HYPOTHESIS · CITED.*
