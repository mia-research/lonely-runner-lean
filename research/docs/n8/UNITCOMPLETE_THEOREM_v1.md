# The n=8 Unit-Complete leaf, closed for representative speeds

2026-09-07. Framework: `lrc_proof_v10_21.md` §5.1, with the bridge repaired as in
`reports/n8_agent_bridge.md`. Artifacts: `experiments/n8/{safe_measure_v1,
divisible_cover_v1, unitcomplete_theorem_v1}.py`. Nothing here verifies LRC(8)
numerically; its truth is known and is not the question.

This closes one of the two leaves that `reports/n8_agent_branch_inventory.md` found
uncovered at `n = 8`, at the same scope (`representative speeds`) that the corpus
already reached for `n = p²` with Theorem N-PSQ-REP.

## 0. Statement

> **Theorem.** Let `E` be a set of 7 distinct positive integers with `gcd(E) = 1`,
> such that some element is divisible by 8 (Case 2), the two residue classes of
> `{1,…,7}` absent from `R_non` are both non-units (Unit-Complete), and every
> `e ∈ E_non` satisfies `e = ρ_e` (representative speeds). Then `x₀(E) ≥ 1`.

Under these hypotheses `|E_non| = |R_non| = 5`, hence `|E_div| = 2`, and
`E = {1,3,5,7,ρ₀} ∪ {8m₁, 8m₂}` with `ρ₀ ∈ {2,4,6}` and `m₁ ≠ m₂`.

## 1. The bridge, stated and proved  `[PROVED]`

`L = lcm(E)`, `N = 8L`. Every `k ∈ [0,8L)` is uniquely `k = b + rL` with `b ∈ [0,L)`,
`r ∈ [0,8)`. Writing `e·b = t_e·L + s_e` with `t_e = ⌊eb/L⌋` and `0 ≤ s_e < L`,

    e·k mod 8L  =  ((t_e + e·r) mod 8)·L + s_e.

Since `0 ≤ s_e < L`, the loneliness condition `e·k mod 8L ∈ [L, 7L]` holds **iff**
`(e·r + t_e) mod 8 ∈ {1,…,6}` (the residue `7` also succeeds when `s_e = 0`, which
only helps). So `k = b + rL` is a witness precisely when `r ∉ bad(e,t_e)` for every
`e ∈ E`, `bad(e,t) := {r : e·r + t ≡ 0 or 7 (mod 8)}`.

**The union runs over all of `E`, divisible runners included.** The manuscript's
`C(r,b)` at `:149` unions over `E_non` only; that is the defect recorded in
`reports/n8_agent_bridge.md`, and the statement above is the repair.

## 2. What a divisible runner contributes  `[PROVED]`

For `e = 8m`: `e·r ≡ 0 (mod 8)`, so the condition is `t_e mod 8 ∈ {1,…,6}`,
**independent of `r`**. With `x = b/L`,

    t_e mod 8 ∈ {0,7}  ⟺  8m·x mod 8 ∈ [0,1) ∪ [7,8)  ⟺  ‖m x‖ < 1/8.

So the runner `8m` contributes exactly the condition `x ∉ B_m := {x : ‖mx‖ < 1/8}`
— a union of intervals of length `1/(4m)` centred at the points `j/m`, of total
measure exactly `1/4`. A divisible runner of speed `8m` is a loneliness condition
for `m` at the same threshold `1/8`.

## 3. Integrality  `[PROVED]`

Every `e ∈ E` divides `L`. Hence in `b`-coordinates the endpoints of `B_m`
(`jL/m ± L/(8m)`) and the floor breakpoints of the non-divisible runners (`jL/e`)
are all **integers**. Every set below is therefore a union of half-open intervals
with integer endpoints, so its cardinality in `b` is exactly `L` times its measure
in `x`, and any nonempty component contains an integer. No rounding term appears
anywhere.

## 4. The safe set of the five non-divisible runners  `[PROVED — exact cell decomposition]`

`S(ρ₀) := {x : ⋃_{e∈E_non} bad(e,⌊ex⌋) ≠ ℤ/8}`, computed by exact rational cell
decomposition on the breakpoints `j/e`, `e ∈ {1,3,5,7,ρ₀}`:

| `ρ₀` | `\|S(ρ₀)\|` | windows |
|---|---|---|
| 2 | **22/35** | 6 maximal windows, uncovered `r ∈ {1},{6},{2,6},{1,5}` |
| 4 | **5/14** | `S(4) = [1/4, 3/7) ∪ [4/7, 3/4)` — two intervals of length `5/28` |
| 6 | **6/7** | 8 maximal windows |

## 5. Proof of the Theorem

**Case `ρ₀ ∈ {2,6}`.** `|B_{m₁} ∪ B_{m₂}| ≤ 1/4 + 1/4 = 1/2 < 22/35 ≤ |S(ρ₀)|`, so
`S(ρ₀) \ (B_{m₁} ∪ B_{m₂})` has measure at least `22/35 − 1/2 = 9/70 > 0` and, by §3,
contains an integer `b`. Any `r ∉ ⋃_{e∈E_non} bad(e,t_e(b))` gives a witness by §1. ∎

**Case `ρ₀ = 4`.** Here `|S(4)| = 5/14 < 1/2`, so the union bound fails and the
structure of `B_m` is needed.

> **Lemma D.** For distinct positive integers `m₁ ≠ m₂`, `B_{m₁} ∪ B_{m₂}` does not
> cover `I = [1/4, 3/7)`, `|I| = 5/28`.

*Proof.* Exact values of `B_m ∩ I` for small `m`:
`m=1: ∅`; `m=2: ∅` (since `3/7 < 7/16`); `m=3: [7/24,3/8)`, length `1/12`;
`m=4: [1/4,9/32)`, length `1/32`; `m=5: [3/8,17/40)`, length `1/20`.

- *(b)* If `m ≥ 6` then `1/m ≤ 1/6 < 5/28 = |I|`, so `I` contains a full period of
  `B_m` and hence a **complete gap** of length `3/(4m)`.
- *(c)* If `m₁, m₂ ≥ 6`: by (b), `I` contains a complete gap `G` of `B_{m₁}`, disjoint
  from `B_{m₁}`, so `B_{m₂}` must cover `G` alone. Two components of `B_{m₂}` meeting
  `G` would leave the gap between them uncovered, so `G` lies inside one component:
  `3/(4m₁) ≤ 1/(4m₂)`, i.e. `m₁ ≥ 3m₂`. Symmetrically `m₂ ≥ 3m₁`. Impossible.
- *(d)* If the smaller index is `1` or `2`, its `B` misses `I` entirely and the other
  must cover `I` alone: for `m ≥ 6` by (b) it cannot; for `m ≤ 5` the table shows
  `|B_m ∩ I| ≤ 1/12 < 5/28`.
- *(e)* Smaller index `3`: `I \ B_3 ⊇ [1/4, 7/24)`, of length `1/24`, which the other
  must cover alone (its complement in `I` is disjoint from `B_3`, so no help there).
  A single component is needed, forcing `1/(4m₁) ≥ 1/24`, i.e. `m₁ ≤ 6`; and
  `B_1, B_2` miss `I`, `B_4 ∩ I = [1/4,9/32)` stops at `9/32 < 7/24`, `B_5 ∩ I` and
  `B_6 ∩ I = [5/16,17/48)` do not meet `[1/4,7/24)`. None works.
- *(f)* Smaller index `4`: `I \ B_4 = [9/32, 3/7)`, length `33/224`, forcing
  `1/(4m₁) ≥ 33/224`, i.e. `m₁ = 1`, whose `B` misses `I`.
- *(g)* Smaller index `5`: `I \ B_5 ⊇ [1/4, 3/8)`, length `1/8`, forcing `m₁ ≤ 2`,
  whose `B` misses `I`. ∎

By Lemma D, `S(4) \ (B_{m₁} ∪ B_{m₂}) ≠ ∅`; being a union of intervals with integer
`b`-endpoints (§3), it contains an integer `b`, and §1 finishes. ∎

## 6. Checks run

- Lemma D verified exhaustively for all `1 ≤ m₁ < m₂ ≤ 80` (3160 pairs): **0 pairs
  cover `I`**; minimum surviving measure `19/420` at `(m₁,m₂) = (3,5)`.
- End-to-end: 198 admissible tuples `{1,3,5,7,ρ₀,8m₁,8m₂}` (`ρ₀ ∈ {2,4,6}`,
  `1 ≤ m₁ < m₂ ≤ 12`), each searched over all `b ∈ [0,L)` and `r ∈ ℤ/8`. Every tuple
  has a good `(b,r)`, and `k = b + rL` was confirmed to satisfy
  `e·k mod 8L ∈ [L,7L]` for all seven runners. Exact integer arithmetic throughout.

## 7. Scope, and what is still open

**Proved:** the Unit-Complete leaf at `n = 8` for **representative speeds**, all three
`ρ₀`, unconditionally — no equidistribution input, no appeal to LRC(8), and no
dependence on any retracted result. This is the exact `n = 2^k` counterpart of
`Theorem N-PSQ-REP`, which the corpus has for `n = p²` and lacked here.

**Open, and each is now precisely stated:**
1. **Actual speeds with `|E_div| = 2`** — `e_ρ = 8q_ρ + ρ` with some `q_ρ ≥ 1`. §4's
   cell decomposition used `e = ρ`; with general `e_ρ` the cells move, so `S(ρ₀)` must
   be re-derived. The pair rule (`bad(e,t)` depends only on `ρ` and `t mod 8`) survives
   and is the tool.
2. **The twin case `|E_div| = 1`** (`|E_non| = 6`, two speeds sharing a residue class).
   Only one `B_m` to dodge, but a sixth non-divisible runner changes `S`.
3. The dropped-unit leaves, whose route `Lemma 11.3a′` has a refuted Case III
   (`E = (1,2,3,4,5,6,64)`, `L = 960`, `b̂ = 839`: `bad(64,55,8) = ℤ/8`).

## 8. Boundary exactness  `[PROVED — re-verified without midpoints]`

The cell decomposition of §4 was first computed by evaluating `⌊ex⌋` at the **centre**
of each cell. That is only sound if the breakpoint list is complete, and it hides
exactly the endpoint behaviour that matters here — `5·(3/5) = 3` and `7·(5/7) = 5` are
both exact hits, so the window `[3/5,5/7)` must be closed on the left and open on the
right or the floors `t₅ = 3`, `t₇ = 4` are wrong at an endpoint.

`experiments/n8/boundary_exact_v1.py` redoes §4 measuring **entry and exit** of every
cell and never an interior point:

- **Completeness.** For every cell `[a,b)` and every `e`, there is no integer `k` with
  `a < k/e < b`. Checked as an exact rational comparison, not by sampling.
  Result: **0 interior breakpoints** across all three `ρ₀`.
- **Entry/exit agreement.** `⌊e·a⌋` (entry; cells are left-closed) equals
  `lim_{x→b⁻} ⌊ex⌋ = ⌊e·b⌋ − [e·b ∈ ℤ]` (exit). Result: **0 mismatches**, and the
  blocked-set union computed at entry equals the one computed at exit in every cell.
- **Measures unchanged:** `22/35`, `5/14`, `6/7`.
- **`B_m` two ways.** Derived from the floor definition `⌊8mx⌋ mod 8 ∈ {0,7}` and from
  the closed form `⋃_j [j/m − 1/(8m), j/m + 1/(8m))`: identical as interval sets, and
  measure exactly `1/4`, for `m = 1..6`.

**Direction of the one inclusion that is not exact.** The coded bad set is left-closed
and right-open. The bridge (§1) has a boundary exception: when `(t_e + er) ≡ 7 (mod 8)`
**and** `s_e = 0`, runner `e` is in fact satisfied. That exception only **removes**
points from the true bad set. So the set used above is a **superset** of the true bad
set, and every conclusion of the form "a safe fibre exists" drawn from it is
conservative — it can only understate the safe set, never overstate it.
