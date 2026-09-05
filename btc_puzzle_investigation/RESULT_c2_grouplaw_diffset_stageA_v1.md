# RESULT — C2 Stage A: χ₂/χ₃/χ₆ on the group-law difference-set, band-confinement bounded

**Date:** 2026-08-02. **Executes** frozen `PREREG_c2_grouplaw_diffset_v2.md`
(SHA `fde3768e9ddcd76e94bd9708f4976b95cee898955f590e1bfe13b2f1b751365b`, experiment-designer
FRAME-CLEAN on re-gate). **Script:** `c2_grouplaw_diffset_stageA_v1.py`.
**Grade:** `[EMPIRICAL — bounded; gate-cleared; fresh-vs-pool-verified null; per-channel plants; 5-seed OOS]`.

Discharges handoff item **C2**: the χ₂ and χ₆ readouts on the group-law difference `x(Pᵢ−Pⱼ)` that the
original run mis-tagged `[parity-void]` and never read are now **read, power-controlled, and bounded.**

## 1. What ran
Group-law difference-set `D={x(Pᵢ−Pⱼ)}` of M=80 band-random points `[d]G`, d uniform in `[2^{k−1},2^k)`,
k∈{40,64,96,128,160,200}, readouts χ₂/χ₃/χ₆ (E₂/E₃/E₆=|Σχ|², exact integer). Null = M-subsets of a
P=800 uniform-random-point pool (inflation `T²/C(P,2)=0.99%`, the frozen P=10·M rung).

## 2. Controls — all fired, both prior defects’ fixes validated
- **Fresh-vs-pool (Defect-1 axis):** 60 fresh M-uniform sets ranked vs the pool null — mean pctile
  E2=0.457, E3=0.578, E6=0.535, all ∈[0.42,0.58] → **PASS** (fresh arm and pooled null
  indistinguishable). The check itself was validated by *failing* at P=5M in smoke (pctile 0.385).
- **C-GLV:** φ-closed ⇒ E₃=E₆=0 exact (E₂=1521 not forced). PASS.
- **Per-channel plants (Defect-2):** E₂-plant fires E₂ (f=0.05: 99856>V₉₉=22500) with E₆=0; E₃-plant
  fires E₃ (55933>13813) with E₆=0; E₆-plant fires E₆ (35533>12999). **Both marginal plants give
  E₆=0** — confirming E₆ reads genuine joint μ₆ structure. The χ₂/χ₆ channels provably have power.

## 3. Result and bound (Rule 5 — a bound, not a closure)
> **No cell screened the two-sided 99th on the same tail across 5/5 fresh-seed OOS** (all 90 cells mid).
> **Band-confinement leaves no detectable character structure in the group-law difference-set** at M=80,
> bounded per channel at:

| readout | null 99th | ε* (coherent class excess) |
|---|---|---|
| **χ₂ / E₂** | 22500 | **≈ 4.75%** |
| **χ₃ / E₃** | 13813 | **≈ 7.44%** |
| **χ₆ / E₆** | 12999 | **≈ 7.22%** |

**Open (not closed):** below the ε* floors; larger M (ladder {400,1024}, P=10·M, background — tightens
~1/M); k-dependence (the shuffled-band secondary, not run here); characters beyond χ₂/χ₃/χ₆; the
contiguous-difference object (degenerate, deferred).

## 4. Compute (Rule 2)
Pool C(800,2)=319,600 gl-diffs once (61s); 2000 subset draws; 60 fresh-check sets (31s); 30 band arms
(23s); 122s wall. Exact-integer signal path; arm regenerated fresh per OOS seed, pool fixed (v2 §0.2).

## 5. Files
`c2_grouplaw_diffset_stageA_v1.py`, frozen `PREREG_c2_grouplaw_diffset_v2.md` (+v1 the gate-failed
record). Reuses the Step-1 group-law-difference harness. C-NEG inherited/recalibrated
(`RESULT_shortscalar_cneg_recalibration_v1.md`).
