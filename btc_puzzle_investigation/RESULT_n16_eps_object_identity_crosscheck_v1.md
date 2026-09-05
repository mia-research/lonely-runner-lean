# RESULT — N16 owed cross-check DISCHARGED: `|u−v|≤½` == `build.eps` (coordinate object only)

**Date 2026-08-18. Grade: `[VERIFIED — exact, 200,000 random + both real puzzle keys; structural
mechanism identified]`.** Curve secp256k1, `y²=x³+7`. Script:
`n16_eps_object_identity_crosscheck_v1.py` (pure stdlib, exact integer; float only for display).
First brick of `ROADMAP_REDIRECT_v3.md` Brick B (the small, no-pre-reg, decisive sub-step).

## The owed question
`CONFIRMED_core_gate_carry_epsilon_zero_v3.md` proved `eps(x)=0 ⟺ |u−v|≤½` for the **coordinate**
flap, but flagged its extension as valid only **"conditional on my `|u−v|≤½` carry being the same
object as `build.eps` — a cross-check I have NOT run against the project script (owed)."** N16 /
§XVIII-H3 carried the same debt: *verify `|u−v|≤½ == build.eps` on the project script.*

The risk was real: the two implementations use **different conventions** — the proof
(`core_gate_carry_proof_v1.py`) uses `ω` with cube-root `BETA` on the `{π, ωπ}` square domain; the
canonical build (`int1_frame_operator_v1.build_secp`) uses `ω²` (`om2`) on a **Gauss-reduced basis**
and selects the **other** cube root.

## What was run
`build.eps` (canonical, `int1_frame_operator_v1.build_secp`) vs the proof's predicate `|u−v|≤½`
(`abs(u−v) ≤ p//2` from `lift_uv`) vs the proof's own carry `carry_c==(0,0)`, on the **same** inputs:
200,000 seeded-random `X ∈ [1,p)` plus the two real puzzle x-coords (#135, #140). All comparisons are
exact integer equalities.

## Result — IDENTICAL
| comparison | result |
|---|---|
| `(build.eps==0)` == `(\|u−v\|≤½)` | **200000 / 200000 — IDENTICAL** |
| `(build.eps==0)` == `(proof carry==0)` | **200000 / 200000 — IDENTICAL** |
| `(\|u−v\|≤½)` == `(proof carry==0)` (proof-internal T2) | 200000 / 200000 — reproduced |
| #135, #140 | both `core=True` on all three objects |
| core fraction (all three) | **0.748925** ≈ ¾ |

## Why it agrees despite `B_SP ≠ BP_SECP` (the mechanism, not a coincidence)
The proof hardcodes `B_SP`; the canonical build uses `BP_SECP`. They differ — **but exactly**:
`BP_SECP = A_SP − B_SP` (and `BP_SECP + B_SP = A_SP = AP_SECP`, `A_SP == AP_SECP`). So the two scripts
generate the **same GLV/Eisenstein lattice** in a **conjugate basis** — proof's `(A, B)` vs build's
`(A, A−B)`, related by the ω-action of the lattice. The `eps=0` core/flap partition is therefore
**basis-choice-invariant**: it is one canonical geometric object, not an artifact of one lift
convention. This *strengthens* the discharge — the object survived a genuine convention change.

## Scope — what this DOES and does NOT settle
- **DOES (discharged).** The **coordinate** flap `eps` is a single canonical object across the project:
  `core_gate_carry_proof_v1`'s `|u−v|≤½` criterion ⟺ `int1_frame_operator.build.eps` ⟺ the ω-carry
  `c==0`. The `CONFIRMED_v3` "owed / conditional on object-identity" caveat and the N16/§XVIII-H3
  cross-check debt are **cleared**.
- **DOES NOT (still OPEN, unchanged).** Whether the coordinate flap `eps(x)` equals the **scalar
  joint-carry** `ε_LBE = [r₁+r₂ ≥ n]` (which contains `d`). `s<3/16` does **not** gate `ε_LBE`
  (`RESULT_eps_to_d_constraint`: 21–93 violations); `eps == ε_LBE` is unresolved and nothing here
  touches it. This brick is about the coordinate object's cross-script self-consistency, not flap==carry.

## Residual (named, small)
The "for **all** X" claim rests on 200k samples + the structural mechanism. To make it exact-for-all-X
`[PROVED]`, prove the two rounding conventions (`rdiv` vs `//(2p)`) agree on the measure-zero domain
boundary given `BP_SECP = A_SP − B_SP`. Not run; not needed for the discharge at the `[VERIFIED]` bar.

## Roadmap consequence
`ROADMAP_REDIRECT_v3` Brick B sub-step 1 (the N16 `|u−v|≤½ == build.eps` cross-check) is **DONE, PASS**.
Next in Brick B: the analytical `eis(X)` public-route question — does the (now-canonical) lift/flap give
a **public** handle on the **scalar** carry — which is the part flap==carry (N16 main) and the arsenal
are gated on. No grade elsewhere moves on this; it removes one caveat and clears one owed debt.
