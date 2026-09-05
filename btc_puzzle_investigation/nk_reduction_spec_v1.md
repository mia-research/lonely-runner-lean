# n/k/D Reduction Spec v1 — LOCKED verified reductions

**Date:** 2026-07-06. **Dataset:** `constructed_keys_1to160_100k.csv` (100,023 keys),
`puzzles_verified.csv` (82 solved real keys). **Curve:** secp256k1.
**Construction:** `d = A + ⌊A·k/n⌋ + D`, `A = 2^(N-1)`, `(n,k)` = best rational approx
of `u=(d-A)/A` with `n ≤ 256`, `D` = residual (`D_terms` = recursion depth).

Every number below is a *measured/derived* reduction with its verification and a confidence
tier. This is the durable record; the operational artifact is `nk_prior_generator.py`.

---

## TIER 1 — EXACT / DETERMINISTIC (mathematically certain, not statistical)

**R1. `N`-conditioning concentrates the `(n,k)` prior.**
- `H(n | N) = 7.78 bits` (peaked; construction measure). Expected `(n,k)`-cell guessing
  entropy drops from **13.28 bits blind → ~12.6 bits** knowing `N`.
- **Reduction: ~0.67 bits (≈1.6×)**, stable to ±0.1 bit across sampling seeds.
- Verified: deterministic Farey-cell measure, 120k uniform-`d` draws (`nk_prior_generator.py`,
  `nk_160_reduction.py`).

**R2. Each `(n,k)` hypothesis bounds `d` to a window (scope pin).**
- `d ∈ base ± w`, `base = A + ⌊A·k/n⌋`, `w ≈ A/(n·n_next) ≈ A/n²`.
- Large `n` (~256): `w ≈ 2^(N-16)` → **top ~16 bits of `d` pinned** (N=160 → 2^144 window).
- ⚠ Small `n` (1,2,4): `w ≈ whole range` → **no scope gain** despite high per-cell prior.
- Verified: `|D|` distribution on 100k, median `bitlen|D| ≈ N-16`.

**R3. `N` pins `D_terms` (within-cell structure).**
- `H(D_terms | N) = 0.50 bits`; `D_terms ≈ 4-5` at N=160. Within-cell reduction **≤ 0.5 bits**.
- Verified: 100k, `corr(bits, D_terms)=0.90`.

---

## TIER 2 — STATISTICAL, REAL-KEY SELECTION (marginal; 82 solved keys vs matched-Farey null)

**R4. Composite / even / low-φ `n` lean.** Reweight `P(n|N)` by:
`n prime ×0.60` (p=0.025) · `n even ×1.27` (p=0.052) · `φ(n)/n<0.6 ×1.25` (p=0.015).
- Adds ~0.14 bits → **N+selection total ~0.81 bits (≈1.76×)**. `KL(real‖uniform)=0.066 bits`.
- Confidence: best single p=0.015; Bonferroni×6=0.09; coherent direction across 5 correlated
  stats (Fisher p=0.0003 but correlated⇒optimistic). Absent from synthetic set ⇒ creator-selection.

**R5. Large-`n` drift (use for HIGH puzzles).** `n≥250` preference weakens with puzzle#
(Spearman −0.236, **p=0.033**). ⇒ for N≥100 use LR `n≥250 ×1.20`, not the pooled `×1.93`.

**R6. `n mod m` residue tilts (candidate, weakest).** `n≡4,5 mod 6` favored (p=0.019);
`n≡3 mod 5` depleted (p=0.037). Heavy multiple-testing exposure. Apply as small tilt only.

---

## TOTAL genuine reduction (puzzle 160)
- `(n,k)`-guessing: **~0.7–0.9 bits (≈1.6–1.8×)** [R1+R4/R5/R6].
- within-cell: **≤0.5 bits** [R3].
- per-hypothesis scope: `d` pinned to **2^144** window (top ~16 bits) for large-`n` cells [R2].
- **Net expected-search reduction ≈ 1.0–1.4 bits** on the 159-bit range.

## BOUNDARY — verified NON-reductions (locked out)
- **`(X,Y) → n/k`: NULL.** Public point leaks nothing about `n/k/D/sign(D)`; full curve-aware
  ML battery at 100k, permutation null, sensitive positive control (z=+115…+202). No per-key reduction.
- **Decomposition alone: no net gain.** Bijective reparam; DLP-cost = `√A · Σφ(n)/n` = **156× worse**
  than direct kangaroo without a prior.
- **`n↔k` does not self-compound** without an independent seed: `k` has zero structure independent
  of `n` (all |z|<0.25); joint = 12.4 bits, coprimality already spent. Compounds ONLY given an
  independent constraint (independent `k`-bit — absent; or a public `(n,k)` seed — absent).
  *(User holds separate propagation math; this spec provides the verified prior it consumes.)*

## Operational artifact
`nk_prior_generator.py <N> [top]` — emits ranked `(n,k)` candidates by `P(n|N)×selection`,
each with base scalar and `d`-window, + the bit accounting. Consumable prior for a
candidate-sweep / propagation pipeline. Re-run trigger: more solved keys sharpen/kill R4–R6.
