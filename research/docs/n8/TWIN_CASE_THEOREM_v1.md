# The n=8 Unit-Complete leaf, twin case (`|E_div| = 1`) — closed

2026-09-07. Companion to `docs/n8/UNITCOMPLETE_THEOREM_v1.md` (which closes
`|E_div| = 2`). Full proof: `reports/n8_twin_case.md` (880 lines); scripts
`experiments/n8/twin3_*.py`. Independently produced, then spot-checked here.

## Theorem  `[PROVED]`

`n = 8`, Case 2, Unit-Complete, `|E_non| = 6` and `|E_div| = 1` — so `E_non` carries
six speeds over the five classes of `R_non = {1,3,5,7,ρ₀}`, one class doubled by a
**twin** `e′ = 8q′ + ρ′` (`q′ ≥ 1`), and `E_div = {8m}`. Base speeds representative.
Then for **every** admissible `(ρ₀, ρ′, q′, m)` — no upper bound on `q′` or `m` — a
safe fibre exists, hence an integer `b`, hence a witness.

## Structure of the proof

**Window criterion.** Choose a window `W = [α,β)` and a non-empty `V ⊆ U(x)` valid for
all `x ∈ W`, where `U(x)` is the set left uncovered by the five base runners. Put
`J = {j : V ⊆ bad(ρ′,j)}` and `A(c,J) = {x : ⌊cx⌋ mod 8 ∈ J}`. Then every
`x ∈ W \ (A(e′,J) ∪ B_m)` is safe.

**Lemma 1 (shape of `J`).** For every `ρ′` and every non-empty `V`, `J` is empty, a
singleton, or a **cyclically adjacent pair**. Hence `A`-components have length `≤ 2/c`
and `A`-gaps `≥ 6/c`. *Verified here independently: exhausted over all 7 × 255 = 1785
pairs `(ρ′,V)`, **0 violations**.*

**Lemma 3 (gap lemma).** If `ℓ ≥ 15/c` and `ℓ ≥ 7/(4m)` then `W ⊄ A ∪ B_m`. The
`A`-free interval of length `≥ 6/c` must fit inside one `B_m` component (`1/(4m)`),
forcing `c ≥ 24m`; the `B_m`-free interval of length `3/(4m)` must fit inside one `A`
component (`≤ 2/c`), forcing `3c ≤ 8m`. Together `72m ≤ 3c ≤ 8m` — impossible.
*Arithmetic re-derived here and consistent.*

**Lemmas 4/5** cut the two residual strips (`c < C₁`, `m < M₁`) to a finite set, leaving
**six cases, 15 `(ρ₀,ρ′)` pairs, 179 residual cells**, each with an exhibited witness.

The `ρ₀ = 4` prediction is confirmed exactly: `V = {1,4}` forces `4 − 1 = ±ρ′`, so only
`ρ′ ∈ {3,5}` can kill the pair, and there `J` is a **singleton** (`κ = 1`).

## Two corrections to the route that was suggested to the prover

1. **"The twin kills at most measure `1/4`" is FALSE.**
   `|A(e′,J)| = (κq′+s)/(8q′+ρ′)` with `s = #{j ∈ J : j < ρ′}`, which exceeds `1/4`
   exactly when `4s > ρ′`. *Verified here:* `|A(13,{1,2})| = 4/13 > 1/4`, and over
   `c ∈ [9,60)` with adjacent `J` the maximum is `2/5` at `c = 10`. The proof above
   therefore uses **no measure bound at all**.
2. **The union bound is negative for `ρ₀ = 4`** (`|S| − max|K| − 1/4 = −15/308` at
   `e′ = 11`), so measure alone cannot close that case — as expected.

Neither correction touches `UNITCOMPLETE_THEOREM_v1.md`: that theorem has no twin, and
its union-bound step uses only `|B_m| = 1/4`, which is exact and was verified two
independent ways.

## The trap, reproduced and dissolved

On the *wider* window `[1/4,3/7)` with `V = {4}` exactly one cell fails:
`(e′,m) = (11,4)`, i.e. `E = {1,3,4,5,7,11,32}` — the tuple that defeated an earlier
attempt of mine that tracked only `r = 4`. On the fine window `V = {1,4}` that cell is
not even residual: `A(11,{4}) = [4/11,5/11)`, so it is settled for all `m ≥ 4`, and the
surviving interval is `[2/7, 4/11)` — exactly where residue `1` survives.
*Verified here end-to-end:* `L = 36960`, `b = 10560`, `r = 1`, `k = 47520`, and
`min_e ‖e·k/(8L)‖ = 1/8` exactly (attained by runner 7); `gcd(E) = 1`; dropped classes
`{2,6}`, both non-units, so the tuple is genuinely in this leaf.

## Controls reported by the prover

Lemma-region controls 39 968 instances / 0 violations; window identity vs brute force
1440/0; Lemma 1 exhaustion 1785/0; **Table 1 recomputed by pure-integer enumeration in
`b`-coordinates, independent of the `Fraction` interval algebra** — matches; all 179
witnesses audited against the full seven-runner set; the bridge checked end-to-end on
all 179; safe-measure sweeps of 54 000 tuples (`q′,m ≤ 60`) and 16 335
boundary-straddling tuples (`q′,m ∈ 1..12 ∪ 280..300`), zero empty safe sets; minimum
safe measure `53/924` at `E = {1,3,4,5,7,11,24}`.

The `b`-coordinate recomputation is the boundary-exactness control this project asks
for: entry/exit rather than an averaged interior point.

## Scope

**Proved:** the twin case with representative base speeds, all `(ρ₀,ρ′,q′,m)`.
**Not settled:** non-representative base speeds (the window criterion survives, but
Table 1 changes and the case table must be recomputed); leaves with two doubled classes;
and no positive lower bound on safe measure is claimed.
