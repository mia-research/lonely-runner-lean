# Pre-registration — the `x = 3` sector of Lemma 7 at `k = 7`, `p = 163`

**Status: PRE-REGISTRATION. Written before any `x = 3` datum is seen. Not a result.** 2026-09-07. This file is the
`experiment-designer` artefact required by CLAUDE.md §2, so no `[PROVISIONAL]` tag applies.

## 1. Object

`n = 8`, `k = 7`, `p = 163`, `N = n·p = 1304`, `H = N/2 = 652`. Targets `j ∈ {1..652}`; speeds `v ∈ {1..652}` with
`163 ∤ v` (648 of them). `v` covers `j` iff `(j·v mod N) < p` or `(j·v mod N) > N − p`. A **bad cover** is a 7-set `T`
of speeds covering every target with `gcd(S ∪ {N}) = 1` for every 6-subset `S ⊂ T`; as `N = 2³·163` and `163 ∤ v`,
that is exactly **`T` has at least two odd speeds**. Classes `C_r = {r, r+163, r+326, r+489}`, `r = 1..163`, members
`t = 0..3`. Sector `x := #{v ∈ T : 8 | v}`; coarse speeds `v = 8w`, `w = 1..81`; the other 567 are non-coarse. **This
cell: `x = 3`** — 3 coarse, 4 non-coarse, at least 2 of the 4 odd.

**Reduction, exact, not a proxy.** By `CAP_TABLE_UNIFORM_v1` a coarse speed covers 0 or 4 of any class. Let `U(C)` be
the classes missed by the coarse triple `C`, so `|U(C)| ≥ U_min(3) = 58`. Then `C ∪ V` covers all 652 targets **iff**
the four non-coarse speeds `V` fully cover every class of `U(C)`; classes outside `U(C)` are already complete, so
nothing is discarded. **Disjointness:** the enumerated feature `U(C)` depends on the coarse triple alone and the
tested property on non-coarse speeds only — `v₂ ≥ 3` versus `v₂ < 3`. No tautology.

## 2. Statistic

**Primary: `K` = the number of bad covers with `x = 3` at `p = 163`** — an exact integer from an exhaustive search,
deterministic, with no sampling null; the only failure modes are implementation errors, and §4 addresses those.
**Exhaustiveness flag `Z`** = number of coarse triples whose search hits the per-triple node cap; the search is
exhaustive iff `Z = 0`. **Secondary, computed whatever `K` is, so that a zero is not a bare bound:** the distribution
of `|U(C)|` over all 85 320 triples, and on a seeded sample of 200 triples the residual deficiency `d(C)` = fewest
classes of `U(C)` left incomplete by any 4-tuple a seeded hill-climb finds, with the type census (odd / `4 mod 8` / `2
mod 4`) of the best near-misses — structure a yes/no answer cannot carry.

## 2a. Branching rule (binding on the implementer)

Enumerate the coarse side, `C(81,3) = 85 320`; forward enumeration of the non-coarse side is `C(567,4) = 4261041855` and is not
attempted. Per triple, depth-4 search over the 567 non-coarse speeds with demand set `U(C)`. State:
distinct chosen speeds `P`, remaining `b = 4 − |P|`.

- **B1 (branch target).** Among incomplete classes of `U(C)` take `r*` with the **most** uncovered targets, ties to
  smallest `r`; `t*` its least uncovered index, `j* = r* + 163·t*`. Branch over **every** non-coarse `v ∉ P` covering
  `j*`.
- **B2 (capacity).** Prune if any class of `U(C)` has more than `2b` uncovered targets — a non-coarse speed covers at
  most 2 targets of a class.
- **B3 (gcd).** Prune if `#odd(P) + b < 2`.
- **B4 (pair type).** If `b = 2` and some class of `U(C)` is wholly uncovered, the two remaining speeds each
  contribute 2 and partition it; an adjacent pair meets an opposite pair, so both must be odd or both `≡ 4 (mod 8)`.
  Restrict candidates accordingly.

**Completeness.** Any solution covers `j*` and no speed of `P` does, so it contains an unchosen speed covering `j*`;
B1 enumerates all of those with no ordering restriction, so that branch is explored (duplicates cost time, not
correctness). B2, B3, B4 delete only states that provably admit no completion — by the cap table, the gcd condition
and the pair-type corollary respectively. **No filter may be added at run time**; pruning beyond B2–B4 needs a new
pre-registration, not an edit here. **Not registered:** the `WLOG 1 ∈ T` depth-3 variant, which needs **L1: unit
scaling preserves `x`**, not on file. If L1 is proved in writing it may be pre-registered separately; never adopted
mid-run.

## 3. Feasibility, measured before the full run

Pilot: 200 coarse triples via `random.Random(20260907).sample` over the 85 320 indices; report nodes explored and
integer milliseconds per triple (min / median / max) and the projected totals `85 320 × mean`. **Budget 6 CPU-hours
single core; per-triple node cap 20 000 000.** **Abort rule:** if the projection exceeds the budget, **do not launch**
— record the measured cost and report `ATTEMPTED-NOT-DECIDED`, a valid outcome. Do not run unbounded and do not retune the rule to fit the measurement.

## 4. Controls — all must pass before any `x = 3` number is reported

- **C1 (forward reproduction of the shared primitives).** `x = 5`: all `C(324,2) = 52 326` odd pairs, **227** pass
  `|D| ≥ U_min(5) = 12`, all fail, NONE. `x = 4`: **2801** triples pass `|D| ≥ U_min(4) = 34`, all fail, NONE.
- **C2 (matched control, inverted mode).** Re-decide `x = 4` with the *same* inverted code — all `C(81,4) = 1 663 740`
  coarse 4-sets, depth 3, same B1–B4 — and obtain NONE; then `x = 5` (`C(81,5) = 25 621 596`, depth 2) if it fits the
  budget, else record it owed with the measured cost. C2 preserves the branching rule, cap-table pruning and gcd
  filter, varying only depth and coarse arity. **It cannot catch a fault specific to depth 4 or to `|U| ≥ 58`** —
  stated now, not after.
- **P1 (primitive plant).** `T₀ = {8,32,40,48,56,88,104}` must be reported as covering all 652 targets and as
  **failing** the gcd condition (`gcd(T₀ ∪ {1304}) = 8`). It has `x = 7`, so it **cannot** be a search plant; it
  validates the cover and gcd primitives.
- **P2 (search plant — must fire).** Seed `20260907`; a 100 000-step hill-climb over 4-tuples `V` of non-coarse speeds with `≥ 2` odd, maximising `|D(V)|` = classes `V` fully covers; keep the best 20. For each, run the
  *unmodified* depth-4 search with demand set `U := D(V)` and the full 567-speed pool. **It must return a solution for
  all 20**; one miss means B1–B4 over-prune and the run is void. Report each `|D(V)|`; if none reaches 58, record the
  maximum and state that the positive control exercised the machinery below the operating demand size — a weakness of
  the plant, not a pass.

## 5. Power

Exhaustive search: detection probability 1 for any bad cover, **conditional on** (a) completeness of B1–B4 (argued in
§2a, exercised by C2 and P2) and (b) `Z = 0`. If `Z > 0` the guarantee weakens to "no bad cover among the `85 320 − Z`
triples fully searched", which is not a decision. If P2 does not fire, the null is uninformative and nothing about the `x = 3` cell may be reported.

## 6. Scope

`n = 8`, `k = 7`, `p = 163`, `N = 1304`, targets `1..652`, speeds `1..652` with `163 ∤ v`, sector `x = 3` only; every
number must be stated as `(p = 163, x = 3)`. Deciding this cell moves the ledger from **2 to 3 of 135 cells**; it
proves nothing about the other 26 primes, nothing about `x = 2` or `x = 1`, and nothing about `n = 8` as a whole.

## 7. Falsification

`H0`: no bad cover with `x = 3` at `p = 163`; one verified bad cover refutes it. A found cover must be printed with
the 7-tuple, the coarse/non-coarse split and `x`, `gcd(S ∪ {1304})` for all seven 6-subsets, and an **independent recheck** by a separate script looping `j = 1..652` over `(j·v mod 1304)` directly for the seven speeds and
confirming 652/652 without reusing the bitmask tables. If that check disagrees with the search, the search is void and
the discrepancy is the finding.

## 8. Exactness

Integers only on the signal path: `int`, bitmasks `& | ~ <<`, `%`, `math.gcd`, `int.bit_count`. No true division, no
float, no `math.sqrt/log`, in computation or in reporting. **Carve-out:** timing by `time.perf_counter_ns()` (integer
nanoseconds) reported as integer milliseconds — analytic size only, never in the signal path. **Named check:** run
`experiments/n8/float_audit_v1.py` (AST audit, not a grep) on the new script and paste its output into the result
file.

## 9. Pre-committed conclusions

| outcome | conclusion, fixed now |
|---|---|
| `K = 0`, `Z = 0`, C1+C2+P1+P2 pass | Sector `x = 3` **DECIDED**: no bad cover at `(p = 163, x = 3)`. Grade `VERIFIED-scope`, scope §6. Ledger 3 of 135. Report with the §2 secondary profile; one cell closes, nothing wider. |
| `K ≥ 1`, independent check confirms | `H0` **refuted** at `(p = 163, x = 3)`. Print per §7 and report the structure used (type census, `\|U(C)\|`). |
| `K ≥ 1`, independent check disagrees | Run **VOID**. The discrepancy is the finding; report both computations and decide nothing. |
| `Z > 0` | **ATTEMPTED-NOT-DECIDED.** Report `Z`, the capped triples, measured and projected cost. Ledger stays at 2 of 135. Not a closure. |
| pilot projection over budget | **Do not launch.** `ATTEMPTED-NOT-DECIDED` with the measured per-triple cost. Any re-scope is a new pre-registration. |
| any of C1, C2, P1, P2 fails | Run **VOID**. Report nothing about `x = 3`; fix and re-register as `_v2`. |
