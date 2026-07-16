# Findings v30 — the joint-SET / difference / cocycle frontier, powered on the 36k constructed set

**Date:** 2026-07-17 · `joint_set_cocycle_v1.py` + inline. Continuing the multi-key / joint-SET
frontier on the **36k constructed keys** (`constructed_keys_fullrange_v1.csv`, known d, real secp
scale, with precomputed `a_glv, b_glv, sextant, chi6X, chi6Y, chi2Y`) — full power, known answers.

## 1. Single-key, powered `[VERIFIED, 8000 keys, 40-shuffle null]`
`MI(feature mod m ; target mod m)`, z vs shuffle, for lift-μ₆ features vs the scalar structure:

| feature\target | a_glv | b_glv | D | d | n | k |
|---|---|---|---|---|---|---|
| sextant, chi6X, chi6Y (mod 6) | z ∈ [−1.8, +1.4] | | | | | |
| chi2Y (mod 2) | **+2.1** (a_glv) | | | | | |
| xy (mod 6 / mod 2) | | | **+1.3…+1.5** (D) | | | |

**All |z| ≤ 2.1** — no lift-μ₆ feature (sextant, chi6, chi2Y, xy) shadows the GLV components,
D, d, n, or k. The known `xy→D` shows only as a consistent sub-threshold `z≈+1.4`. The single-key
channel is a **powered** null (vs the underpowered 82-key look).

## 2. ★ The cocycle / ≥3-key test — is xy chainable?  `[VERIFIED, controls FIRE]`
The right joint-SET object: a cheap readout that **chains** (`r(P+Q)=f(r(P),r(Q))`) would let
per-point info **accumulate** (`√N` coherent bias) into a joint-SET reduction of `{d_i}`. Test:
`MI(f(S) mod 6 ; (f(P) mod 6, f(Q) mod 6))`, `S=P+Q`, 3000 triples, z vs shuffle.

| readout | MI | z | verdict |
|---|---|---|---|
| **d** (control: additive cocycle) | **2.584 = log₂6 (max)** | **+648** | detector fires — perfect cocycle |
| random (control: null) | 0.040 | −0.9 | correct null |
| **xy** (the test) | **0.042** | **+0.0** | **NOT a cocycle — at the random level** |

**xy is not a cocycle** — `xy(P+Q)` is not determined by `xy(P), xy(Q)`; it sits exactly at the
random-readout level, with a detector that fires at z=648 on a genuine cocycle. **⇒ per-difference
xy-shadows do NOT chain ⇒ no `√N` accumulation ⇒ no joint-SET handle from xy** via the
difference/cocycle structure.

## 3. Synthesis — the joint-SET frontier, tested from four angles with firing controls
- single-key (v29/v30): **powered null** (8000 keys, all |z|≤2.1).
- bilinear additive (v28): **powered null** (planted rank-1 levers fire at max/n=n and 0.3n).
- multiplicative (pairing): **absent by MOV** embedding degree ~254-bit `[CITED]`.
- cocycle / ≥3-key (v30): **powered null** (xy z=0 vs cocycle control z=648).

**The concrete positive that emerges:** `d` is the **unique additive cocycle** (MI maximal, z=648),
and **no cheap readout — including the odd+μ₃-covariant `xy` — approximates it.** This is the
parity-obstruction model made quantitative: the only chaining/accumulating readout of the point IS
the scalar d (= the DLP). The real `xy` structure (odd+μ₃-covariant, equal-mass shadow, single-key
D-shadow) does not lift to a joint-SET reduction because it does not chain.

## Scope / genuinely still open (NOT a closure)
- `m=6/2` modular resolution (the known `(X·Y)mod64→D` is mod 64 — a finer-m difference-set scan is
  untouched); 8000/3000-sample power; the **difference-set distribution geometry** (eis cubic moment,
  eps/norm-band of pairwise differences) is `bilinear_jointset_harness_v1`'s separate probe.
- **Higher-order multilinear** (≥4-key relations, the Semaev S₄ relation among key-differences) —
  untouched. **secp's full range** vs bucketed scale.
- An empirical null is a scoped fact; the frontier is not closed, but from four powered, controlled
  angles the joint-SET xy handle is absent at these objects/scales.

## Grades
- Single-key powered null: **VERIFIED** (8000 keys). Cocycle null with firing control (d z=648,
  xy z=0): **VERIFIED**. `d` = unique additive cocycle: **VERIFIED/structural**. Multiplicative
  absent: **CITED** (MOV). No self-cert words; null stated scoped; the xy structure stated positive.

## Files
`joint_set_cocycle_v1.py`, inline feature-correlation on `constructed_keys_fullrange_v1.csv`. Prior:
`masked_structure_findings_v26/v28/v29.md`, `bilinear_jointset_harness_v1.py`,
`KNOWN_FACTS_secp256k1_and_keys_v5.1.md` (parity-obstruction, MOV).
