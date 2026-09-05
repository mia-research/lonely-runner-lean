# CONFIRMED — the COORDINATE flap `eps(x)` is decidable exactly from x alone (v3, corrects the object-identity declaration of v1/v2)

**v3 fixes a "closing-by-declaration" error in v1/v2**, caught in self-audit against
`RESULT_linchpin_s_gate_v2.md`. Date 2026-08-16. Curve secp256k1, `y²=x³+7`.

## The correction (what v1/v2 got wrong)

v1/v2 named the proved object "ε (GLV coordinate carry) … **the exact ε the Core Gate
refers to**." That parenthetical **asserts an identity the project holds OPEN**:

- **`eps(x)`** — the Cap-Law coordinate flap, exact integer function of `x` ALONE (no `d`).
  **This is what is proved below.** Same object as `int1_frame_operator.build.eps`.
- **`ε_LBE`** — the scalar joint-carry `[r₁+r₂ ≥ n]`, which **contains `d`**. `s<3/16` does
  **NOT** gate it (`RESULT_eps_to_d_constraint`: 21–93 violations). Whether `eps == ε_LBE`
  is **UNRESOLVED** (`RESULT_linchpin_s_gate_v2` §"Two distinct objects"). Nothing here
  closes it.

The project's own linchpin v1 made this identical over-record and its v2 retracted it.
v3 does the same: the PROVED statement is a **public-map fact about the coordinate flap**,
not a statement about the `d`-carry.

## What is genuinely PROVED + VERIFIED (coordinate object only)

`eps(x) = 0  ⟺  |u−v| ≤ ½`, where `(u,v)` is the centered lift of `x`. Total, exact, O(1),
`x`-only. Derivation: `ω·(u,v)=(−v,u−v)`; `|v|≤½ ⇒ round(−v)=0`; `max|u−v|` on `s=u²−uv+v²`
is `2√(s/3)`, so `s<3/16 ⇒ eps=0` (sufficient) and `s≤¼` necessary. Verified:
- 2,000,000 random lifts: 0 violations; max `s` at `eps=0` = 0.2496 (≤¼); boundary on `3/16`.
- `eps=0` locus **exactly 3/4 = 75%** (empirical 74.97%); gate `s<3/16` = **`π√3/8` = 68.02%**
  (empirical 67.93%); gate ⊂ hexagon (0/200k).
- #135 `s=0.0589`, #140 `s=0.0198` → both `eps=0`, carry `(0,0)` vs the actual `βx` lift.

**This reproduces `RESULT_linchpin_s_gate_v2`** (secp: `Pr[s<3/16]=0.68`, `Pr[eps=0]=0.75`,
0 violations) and **extends it** with the exact `⟺ |u−v|≤½` hexagon criterion, the total
decision (all keys), the `¾` locus, and the `¼` necessary bound. The extension is valid
**conditional on my `|u−v|≤½` carry being the same object as `build.eps`** — a cross-check
I have **not** run against the project script (declared, not tested; owed).

## What is NOT established (kept open, not declared either way)

- **NOT** that this is the `d`-carry `ε_LBE`. That identity is open (`linchpin_s_gate_v2`).
- **NOT** any `d`-side consequence. `s<3/16` and the scalar carry are independent
  (`RESULT_score_exclusion_rangecut`: Fréchet floor + 6648 counterexamples).
- **Owed:** verify `|u−v|≤½` == `build.eps` on the project script; `citation-verifier` on
  the Cap-Law `¾:⅛:⅛` inputs before any grade moves up.

Supersedes v2's object-identity claim; the geometry in v2 stands. Related:
[linchpin_s_gate_v2](RESULT_linchpin_s_gate_v2.md), [v2](CONFIRMED_core_gate_carry_epsilon_zero_v2.md).
