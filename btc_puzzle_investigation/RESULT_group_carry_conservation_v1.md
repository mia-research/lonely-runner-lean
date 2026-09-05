# RESULT — the group-side carry conservation (P17's twin) + the additive↔multiplicative orbit bridge

**Grade: `[VERIFIED — exact, 4998/4998; small scale n≤4999]`.** Date 2026-08-17. Explores the additive and
joint-set sides flagged in `REFLECTIONS_frobenius_face_synthesis_v1`. Extends `RESULT_group_carry_gate_v1`
(the group carry `ĉ`). Ties to the field-side conservation **P17** (`NOTE_glv_orbit_carry_conservation_v1`,
master row P17). Exact ℤ[ω] arithmetic. No master edited.

## Setup
Group carry `ĉ(d) = (ω·D(d) − D(λ_π d))/π_n`, re-centered `∈ {0,±ω}` with the ¾ law
(`RESULT_group_carry_gate_v1`). `D(d)` = lift of scalar `d` to the fundamental domain of `π_n`.

## Finding 1 — the ADDITIVE orbit carry lives in the ramified-prime direction
Generic additive carry `ε_add(a,b)=(D(a)+D(b)−D(a+b))/π_n` takes **9** values. But the **λ-orbit** triple
carry `ε₃(d)=(D(d)+D(λd)+D(λ²d))/π_n` (well-defined because `d+λd+λ²d≡0`, since `1+λ+λ²≡0`) collapses to a
clean **`{¾, ⅛, ⅛}`** law with values `{c₀, c₀±(1−ω)}`.
- `N(1−ω) = 3` = the **ramified prime**. The orbit carry moves along `(1−ω)`, exactly the project's known
  carry-geometry direction (`KNOWN_FACTS`: *"strip direction is `(1−ω)π`; `3 = −ω²(1−ω)²`"*). The additive
  orbit carry is a **ramified-prime-3 object**.

## Finding 2 — the additive↔multiplicative BRIDGE (exact, 4998/4998)
`ε₃(d) = −( ĉ(d)·(1+ω) + ĉ(λd) )`. The additive orbit carry is **determined by the multiplicative carries**
`ĉ(d), ĉ(λd)`. So the two carry families — which are uncorrelated *pairwise* (`MI(ĉ; ε_add)=0`,
`RESULT_group_carry_gate` follow-up) — are **linked around the orbit** by `1+ω+ω²=0`. "Separate families"
was true pointwise; false around the orbit closure.

## Finding 3 — the GROUP-SIDE CARRY CONSERVATION (exact, 4998/4998) = P17's twin
`ω²·ĉ(d) + ω·ĉ(λd) + ĉ(λ²d) = 0` for **every** `d` (single value, both raw and re-centered `ĉ`).
- This is the exact scalar/group analog of field-side **P17** `ω²c(X)+ωc(βX)+c(β²X)=0`. The carry conserves
  around the λ-orbit (group face `π_n`) exactly as around the β-orbit (field face `π_p`).
- Consequence: the three orbit carries are **not independent** — any two determine the third. The per-orbit
  carry data is **2-dimensional**, not 3.

## Why this is the joint-set object, and what it does / doesn't do (honest)
The reflection flagged joint-set tests as "the only ECDLP-surviving class." This conservation is exactly a
**joint (3-point orbit) exact law** — and it is the *right* structural groundwork:
- **It is a FORCED SYMMETRY of the carry coordinate system.** Because it holds for *every* orbit, it does NOT
  distinguish keys — it does not leak `d` (same fate as P17: a curve invariant, d-homogeneous). No overclaim
  here: this is structure, not a break.
- **But it is what any future joint-set leak test must MATCH-CONTROL for.** Per project doctrine ("a matched
  null shares the signal's forced symmetries"), a joint-set test phrased in carry coordinates must preserve
  `ω²ĉ + ωĉ(λ·) + ĉ(λ²·) = 0` and the bridge — or it will manufacture a spurious signal (exactly the
  residue-vs-component tautology failure mode). This finding *supplies the forced symmetry* to control for.
- **It completes the carry-conservation across both Frobenius faces:** P17 (field) + this (group). The carry
  ¾-law, its gate, and its orbit-conservation now all have field and group twins — the Frobenius-face
  synthesis is closed on the carry side.

## Scope / caveats
- Exact but small scale (`n ≤ 4999`); the conservation and bridge are algebraic identities of ℤ[ω] reduction
  (so expected to hold at all scales), but only verified small here.
- The `{¾,⅛,⅛}` orbit-carry law and the `(1−ω)` direction are the re-centered/associate-dependent
  presentation; the *conservation* `=0` is associate-independent and is the robust core.
- d-homogeneous: a structural invariant, not a per-key leak — stated plainly, no closure claimed and no leak
  claimed.

## Next (additive & joint-set, continued)
- The additive carry `ε_add(a,b)` (9-valued) as a **2-cochain**: is its associativity cocycle a coboundary
  (trivial) or does it carry a class? A non-trivial class would be a genuinely new additive invariant.
- Phrase a joint-set test on a key SET in carry coordinates, **match-controlling for the conservation +
  bridge** found here — the first such test with the forced symmetry known.
- The `ε_LBE` (known d₁ + unknown d₂) additive bit re-cast in this exact ℤ[ω] additive-carry language.
