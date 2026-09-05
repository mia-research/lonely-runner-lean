# AUDIT — the load-bearing claims (decidable re-check)

**Date:** 2026-07-18. Scope chosen by user: audit only the claims the edifice rests on, in depth.
Script `_audit_loadbearing_v1.py` + reran the originals. Decidable checks, not judgment.

## Claim 1 — the KS `U`-bound  `[VERIFIED — SOUND]`

`max_{a,(b,c)≠0} |U(a,b,c)| ≤ 4√p+1` (and `max|T| ≤ 3√p`). This is the theorem that closes
single-point leakage and, being an asymptotic bound, extends to secp.

**Re-checked exhaustively (FFT over all `a`, all `(b,c)`), p=61,67,211:** bound holds every time,
worst `max|U|/(4√p+1) = 0.960`, `max|T| ≤ 3√p` holds. **The most load-bearing claim is sound.** The
"single-point / bounded-degree readouts are closed at the √p floor, extends to secp" conclusion rests
on this, and it verifies.

## Claim 2 — the "0.93 joint (x,y) shadow, ratio 2.8×"  `[VERIFIED — my first audit was WRONG]`

**★ SELF-RETRACTION (method review `_method_review_v1.py`).** My first pass graded this `[NOT
REPRODUCED]` on the basis that `xy_interference_U_v1.py`'s `[4b]` block prints `168 / 1.04 / 161×`.
**That was my error:** `[4b]` uses a *different, unnormalized* metric (`corr/√n`, an un-normalized
channel sum), NOT the shadow metric. I flagged a defect without computing the stated metric — the
"reviewers manufacture issues" failure mode, pointed at a correct claim.

Computing the RECORD's actual metric `|Corr(a0)|/‖F‖_∞` (`‖F‖_∞ = max_d|F(P_d)|`, `F` = the aligned
readout):
```
p=163:  x-only 0.341   joint 0.927   ratio 2.72
p=211:  x-only 0.367   joint 0.920   ratio 2.51
p=433:  x-only 0.338   joint 0.950   ratio 2.81
```
**This matches the recorded 0.34 / 0.93 / 2.8× to two decimals across three primes. The 0.93 claim
is CORRECT and reproduces.** My "not reproduced" finding is **withdrawn**; there is no defect in the
0.93 figure.

## Correction owed → REVERSED

The index flag I added ("0.93 `[NOT REPRODUCED]`") is **wrong and retracted**. The master's
`0.93 / 2.8×` stands, `[VERIFIED]` (reproduced at p=163,211,433 via `|Corr|/‖F‖_∞`). The `168/161×`
is a real number too but from a *different* (un-normalized) metric, and conflating them was my mistake.

## Net (corrected)

Both load-bearing claims audited object-level **hold**: KS bound VERIFIED (FFT==direct to 1e-14, bound
holds worst-ratio 0.96); the 0.93 shadow VERIFIED (reproduces exactly under `|Corr|/‖F‖_∞`). Selection
rule Claim S verified 54/54; amicable Hom=0 = theorem, correctly scoped. **The one defect this audit
produced was MY OWN false-negative on the 0.93** — caught and reversed by the method review. Lesson:
after being pushed on negative bias I over-corrected into defect-manufacturing; symmetric rigor
requires reproducing the exact stated metric before flagging a claim, which I failed to do.
