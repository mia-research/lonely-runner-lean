# RESULT — hard exclusion (empty cells): NONE at populated granularity → redirect to SOFT exclusion. Fence premise (no wall).

**Date:** 2026-08-16. **`[EMPIRICAL — scoped null on HARD exclusion; NOT "impossible"]`.** Gate-free
occupancy characterization (support question, not a matched-null verdict). **Artifact:**
`scratchpad/exclusion_occupancy_v1.py`. Exact integer occupancy counts.

## Question (the NEGATIVE reframe)
Is there an UNFORCED empty cell in the joint (public invariant vector `V(x,y)`, `d mod k`) — a
combination that NEVER occurs — giving a HARD exclusion "observing `V=v` proves `d ≢ r`"? Power
constraint (surfaced by the gate before it hit its weekly limit): with a big joint `V`, `|V|·k > n` ⇒
cells are sampling-empty, meaningless. So test at POPULATED granularity `|V|·k ≪ n` (expected ≥5/cell).

`V` covariants (all public, all μ6-covariant so the GLV orbit adds no new info — μ6 saturation):
χ3-index, flap `eps` (μ3-invariant), sextant (φ:+2), `s`-band, `χ2(y)` (φ-invariant). Targets
`d mod k`, `k∈{2,3,4,6,7}`.

## Result — ZERO empty cells at every populated combo
Curves m=1249, 2143. Single invariants and pairs/triples (up to 84 cells, expected ≥5): **`killed-res
= 0/k` for every feature value; min cell occupancy always > 0.** Every `(V=v, d mod k=r)` occurs.

- **Scoped null on hard exclusion** at these curves/granularities. Under the FENCE premise this is NOT
  "exclusion impossible" — it is bounded to the tested power/scale; secp-scale (`n≈2²⁵⁶`) is unreached.
- Structural reason (empirical, not a wall claim): the point-invariants and `d mod k` do not produce a
  forbidden pair at this scale; the forced μ6-relations relate invariants across the orbit, not to
  `d mod k`, so they force no residue exclusion. `eps` is constant on the μ6-orbit while `d mod k`
  varies over it ⇒ `eps` excludes no residue.

## The live redirect — SOFT exclusion (this is NOT a null)
No cell is empty, but occupancy is **uneven**: e.g. sextant × `d mod 7` has min-occupancy 24 vs
expected 51 — cells markedly under-represented. A significant under-representation is a **soft
exclusion** (bits removed probabilistically from `d`'s range), a real gate if it survives a matched
control. That is the powered mean/deviation test = the reopened **T2d** (public readouts → residue of
`d`), where a raw non-uniformity hint already appeared (χ3=2 row 32/37/43). Hard-empty is one end of a
spectrum; the soft end is where any structure at reachable scale lives.

## Owed / next
- **T2d soft-exclusion, PROPERLY POWERED, pre-registered** (experiment-designer; weekly gate reset
  2026-08-16 15:00): features {χ3, eps, s-band, sextant, χ2(y)} vs `d mod k`; the statistic is
  per-cell under/over-representation vs a matched null that preserves the μ6-forced structure and both
  marginals; measure bits removed; quotient forced relations; both key sets; larger `U`; OOS.
- **Parallel fence-line (open, not closed):** is any public invariant of `[d]G` computable from `d` in
  < one scalar-mult? GLV φ proves ≥1 exists. Not tested here; kept live.
