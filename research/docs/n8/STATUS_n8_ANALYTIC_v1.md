# Analytic n=8: consolidated status

2026-09-08. Supersedes nothing; this is the single place the n=8 case tree, what is
proved, and what is open are recorded together. Sources: `UNITCOMPLETE_THEOREM_v1.md`,
`TWIN_CASE_THEOREM_v1.md`, `DROPPED_UNIT_THEOREM_v1.md`, `NONREP_STATE_v1.md`,
`reports/n8_*.md`, `experiments/n8/`.

Rosenfeld 2025 establishes that LRC(8) is **true**. It supplies no proof of why. The
target here is an analytic argument, and nothing below uses LRC(8) as an input.

## 0. The framework  `[PROVED]`

`E` = 7 distinct positive integers, `gcd 1`, `L = lcm(E)` (every `e ∈ E` divides `L`),
`N = 8L`, `x = b/L` for integer `b ∈ [0,L)`.

**Bridge.** Every `k ∈ [0,8L)` is uniquely `k = b + rL`, and
`e·k mod 8L = ((⌊eb/L⌋ + e·r) mod 8)·L + s_e` with `0 ≤ s_e < L`. So `k` is a witness
iff `(e·r + ⌊ex⌋) mod 8 ∈ {1,…,6}` for **every** `e ∈ E`. The union must run over all
of `E`; `lrc_proof_v10_21.md:149` unions over `E_non` only, which was measured at 37.4%
false positives.

**Pair rule.** Every unit of `ℤ/8` is self-inverse, so a unit runner of residue `ρ`
blocks `{−tρ, −(t+1)ρ}` — one odd, one even, differing by `ρ`. It depends only on `ρ`
and `t mod 8`, **not** on the actual speed `8q+ρ`. Non-units block inside one parity
class. A runner `8m` blocks everything exactly on `B_m = {x : ‖mx‖ < 1/8}`, measure
`1/4`, independent of `r`.

**Integrality.** All breakpoints sit at integer `b`; counts equal `L` × measure exactly.

**B-lemma.** `|B_{m₁} ∪ B_{m₂}| ≤ 1/2 − gcd(m₁,m₂)/(4·max(m₁,m₂)) < 1/2`. So a safe set
of measure `≥ 1/2` always survives two divisible runners.

**Dilation theorem `[PROVED, new]`.** `|S(λ·E_non)| = |S(E_non)|`, and likewise for the
auxiliary measures `o` and `u` of §3. *Proof.* `⌊λe·x⌋ = ⌊e·(λx)⌋`, so the state at `x`
for `λE` is the state at `λx` for `E`; and safety is invariant under `w ↦ w+1` because
`e(r+1) + ⌊ew⌋ = e·r + ⌊e(w+1)⌋` — the free residue `r` absorbs the shift. Hence
`S(λE)` is a `λ`-fold contraction of a period-1 set, of the same measure. ∎
*Checked:* `|S| = 5/14` for `λ = 1,3,5,7,9,11` on `{1,3,5,7,4}`, and `22/35` on
`{1,3,5,7,2}`.

## 1. The case tree

| leaf | representative speeds | non-representative |
|---|---|---|
| Case 1: no multiple of 8 | `t = 1/8`, one line | same |
| Case 2, dropped unit (≥1 absent class is a unit) | **PROVED** | (NR) |
| Case 2, Unit-Complete, `\|E_div\| = 2` | **PROVED** | (H′) |
| Case 2, Unit-Complete, `\|E_div\| = 1` (twin) | **PROVED** | — |

**Dropped-unit** (`DROPPED_UNIT_THEOREM_v1.md`): the union bound settles all 18
absent-pairs; 13 of 18 have `S = [0,1)`, and the extremal is absent `(3,4)`,
`|S| = 19/35 > 1/2`. The single-residue trap is load-bearing exactly once — window
`[3/7,4/7)` has uncovered `{2}` on `[3/7,1/2)` and `{5}` on `[1/2,4/7)`, no residue
valid throughout; tracking one residue gives `|S| = 2/5` and the bound fails.

**Unit-Complete** (`UNITCOMPLETE_THEOREM_v1.md`): `|S(2)| = 22/35`, `|S(6)| = 6/7` fall
to the union bound; `|S(4)| = 5/14 < 1/2` needs **Lemma D** — `B_{m₁} ∪ B_{m₂}` never
covers `[1/4,3/7)`, by the gap structure forcing `m₁ ≥ 3m₂` and `m₂ ≥ 3m₁` at once.

**Twin** (`TWIN_CASE_THEOREM_v1.md`): a window criterion plus a gap lemma, 179 residual
cells each with an exhibited witness. Uses **no measure bound** — and a measure bound
there is outright false (`|A(13,{1,2})| = 4/13 > 1/4`).

## 2. Non-representative: what is proved

- **Reduction `[PROVED]`.** `g = gcd(E_non)` is odd (some base speed is `≡ 1 mod 8`).
  If `g ≥ 3`, the shift `t ↦ t + 1/g` fixes `Ū_{E_non}`, the two divisible runners meet
  fewer than `g` of the shifts, so `E_non/g` — five speeds — would have to cover at
  threshold `1/8`, contradicting **LRC(6)**. Only primitive `E_non` remains.
- **Fibre criterion `[PROVED]`.** For a fixed unit 4-tuple `(e_1,e_3,e_5,e_7)` the whole
  infinite fibre over `ρ₀ ∈ {2,4,6}` and `e_{ρ₀} = 8q+ρ₀` is decided: exact identities
  for `|S^c|`, plus a discrepancy lemma (`P` periodic of period `p` and density `δ`,
  `X` a union of `n` intervals ⟹ `||X ∩ P| − δ|X|| ≤ nδ(1−δ)p`) give
  `|S^c| ≤ (o+u)/2 + (n_U + 3n_O)/(4M)` for `ρ₀ = 4` and `|S^c| ≤ o + n_O/M` otherwise,
  with `M = e_{ρ₀}/4` resp. `e_{ρ₀}/2`. So each fibre needs only a finite check.

## 3. The open statement, exactly  `[OPEN]`

For the four unit runners set `O = {x : all four odd residues blocked}`, `o = |O|`;
`U = {x : all of ℤ/8 blocked}`, `u = |U| ≤ o`. Both are dilation invariants.

> **(H′)** For every **primitive** unit 4-tuple other than `(1,3,5,7)`, the fibre
> criterion closes.

Given (H′), together with §2's reduction, the Dilation theorem, and Lemma D for the one
primitive exception, the non-representative case closes and with it n=8.

**Evidence.** Exhaustive `q ≤ 5` (1296 unit tuples): `ρ₀ = 2` and `ρ₀ = 6` close
1296/1296; `ρ₀ = 4` closes 1293/1296, the three failures being exactly
`(1,3,5,7)`, `(9,3,21,15)`, `(25,35,5,15)` — the dilation orbit of `(1,3,5,7)`. Largest
finite-check threshold `M < 187`. Exhaustive `q ≤ 12` on the base tuples (369 886
primitive per `ρ₀`, speeds ≤ 103): the **only** tuple with `|S| ≤ 1/2` is
`(1,3,5,7,4)` at `5/14`. Random `q ≤ 400` (speeds ≤ 3207): `min |S| ≈ 0.87`.

**What is NOT true, and was checked.** The orbit is a strict outlier — `u+2o = 37/35`
for every member at arbitrarily large speeds, against `≤ 0.684` for everything else —
so no bound on the speeds alone can close (H′); the orbit must be removed by
primitivity, which is exactly what §2's reduction does. And the primitive a-priori
failures are **not** finite: 57 at `q ≤ 6`, occurring at every max speed up to the
sweep limit, so (H′) cannot be reduced to a finite check by the a-priori test alone.

**The route.** `u + o ≤ 3/5 < 1` in every tuple observed, and the crude a-priori test
`u + 2o ≤ 1/2` is lossy — it discards `|A| = 1/2` and `|A'| = 1/4`. Under independence
`|S^c| = (u+o)/2 ≤ 3/10`, comfortably closing. So (H′) is a **discrepancy** statement,
and the natural attack is to iterate the fibre argument over the unit speeds in turn
(`e_7`, then `e_5`, then `e_3`), each step trading a runner for an explicit error term,
until only a finite base remains.

## 4. Grades

Framework, bridge, pair rule, integrality, B-lemma, dilation theorem: **PROVED**.
Three leaf theorems at representative speeds: **PROVED**. Reduction for
`gcd(E_non) ≥ 3` and the fibre criterion: **PROVED**. (H′) and (NR): **OPEN**, with the
evidence and the two negative results above attached.
