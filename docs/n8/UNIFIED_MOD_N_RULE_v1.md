# One rule, in mod-n form, for every configuration

2026-09-13. n = 8, individual isolation, threshold 1/8. Unifies the separate treatments of
AP ± ε, grids at large speeds, and non-grid integers into a single statement.

---

## 1. The rule

For runner `i`, with `d_min` the smaller of its two adjacent gaps:

1. **Candidate interval** — `[ 1/(8·d_min),  7/(8·d_min) ]`, fixed by its two neighbours alone.
2. **Normalise** every other difference: `s = d / d_min`.
3. **Blocked** ⟺ some `s` lies **within 1 of a multiple of n = 8** — a grid multiple, `± 1`.
4. Not blocked ⟹ the moment is `1/(8·d_min)` exactly. Blocked ⟹ it is later, inside the same
   interval.

This is the mod-n form: the band is `8k ± 1`, in units of the runner's own `d_min` rather than in
units of 1.

## 2. It covers every family  `[VERIFIED — 11,200 of 11,200]`

| family | runner-instances | grids among them | agrees with BSM |
|---|---|---|---|
| AP exactly | 1,600 | 200 | **1.000000** |
| AP ± 1/100 | 1,600 | 0 | **1.000000** |
| AP ± 9/10 | 1,600 | 0 | **1.000000** |
| grids, runners pushed out | 1,600 | 200 | **1.000000** |
| non-grid integers `[1,80)` | 1,600 | 0 | **1.000000** |
| rationals, denominators ≤ 29 | 1,600 | 0 | **1.000000** |
| dilated APs, `k = 1..20` | 1,600 | 1 | **1.000000** |

Plus 24,000 on random integer 8-sets in `GENERAL_MOMENT_RULE_v1` §2 — same criterion, same result.

## 3. The earlier rules are its special cases

| earlier statement | is this rule with |
|---|---|
| grids: *keeps `1/8` iff no difference `≡ 0 mod 8`* | `d_min = 1`, integer speeds |
| grids of gcd `g`: blocked iff `d ≡ 0 mod 8g` | `d_min = g` |
| AP ± ε: only index gaps `≥ 7 − 16ε` can block | the band reachable at that ε |
| `R8_INTEGER_LAW_v1`, `R7_R8_PAIR_LAW_v1`, `BLOCK_PUSHOUT_LAW_v1` | the same band, applied per family |

The residue-mod-8 machinery was never a separate theory for grids. It is what the band test
becomes when `d_min = 1` makes `s` an integer.

## 4. And it explains the end runners in one line

At the AP every `d_min = 1`, so `s = d`. The largest difference each runner has:

| runner | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 |
|---|---|---|---|---|---|---|---|---|
| max `s` | **7** | 6 | 5 | 4 | 4 | 5 | 6 | **7** |
| distance to 8 | **1** | 2 | 3 | 4 | 4 | 3 | 2 | **1** |
| | **edge** | in | in | in | in | in | in | **edge** |

**Only r1 and r8 reach 7, exactly 1 from the band edge.** Everyone else tops out at 6 or less, a
clear 2 away. So r1 and r8 are the only runners a small perturbation can tip into blocking.

That single fact accounts for everything the series found about the ends: zero reserve, zero
duration at the AP, no fair band in service, the r1–r8 wrap coupling, the misses concentrating on
them at small ε, and why moving r1 down delays r8 with no runner in between.

## 5. Status and scope

`[VERIFIED — 11,200 of 11,200]` §2's seven families; `[VERIFIED — 24,000]` the same criterion on
random integer sets.
`[PROVED — arithmetic]` §1's steps 1–3 and §3's reductions; §4's table.
`[VERIFIED — 21,600]` that the moment lies in the first candidate interval
(`NEIGHBOUR_INTERVAL_v1`).

**Scope.** n = 8 throughout. Irrational speeds use identical arithmetic but were not swept.

**Not established.** A proof that the good set always meets the first candidate interval — the one
observed-but-unproved step in the chain. Whether the rule's form survives to other n, where the
band would presumably be `nk ± 1` in units of `d_min`.

**n = 8 is not proved here, and is not the target here.**
