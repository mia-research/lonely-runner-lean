# Arrangement transformations: what each preserves (v1, 2026-10-03)

Objects: readings `rho_1 = 1 < ... < rho_7` (speed minus the subject's, units of the smallest), `R >= 1`, zones `((8j-1)/rho, (8j+1)/rho)`, `j >= 1` (the code's `blocks` also includes `j = 0`, which matters only for a start below 1). The cascade `path(rhos)` starts at `R_0 = 1/min`. All runs exact `Fraction`. Library `equiv_lib_v1.py`; one script and one `.out` per transformation (`equiv_t1_v1` ... `equiv_t6_v1`, `equiv_classes_v1`). Pools: 3,500 arrangements per transformation (about 60% with at least one cascade move; log-uniform, AP-deformed, integer, small-denominator, clump), several trials per arrangement.

Notation. `S` = the state sequence `R_0..R_n` (landing `R* = R_n`); `I` = identity-labelled path (tuple position, lap); `P` = rank-labelled path (rank after sorting, lap); `L` = landing `R*`; `O` = opener (the last step); `C` = closer (first zone entry after `R*`); `E` = its entry value. A reading is *inert at S* if it is clear at every state in `S`, landing included.

Two facts used throughout (both exact, both run):
- **F1 (landing = first unblocked point).** `L(s)`, the landing of the chain started at `s`, equals the least unblocked `R >= s` (right end of the component, containing `s`, of the union of open zones). Independent sweep of the zone union against the chain: 8,400 of 8,400 equal (`equiv_t4_v1.out`, part D). Reason: each jump goes to the exit of a zone containing the current point, so no unblocked point is skipped.
- **F2 (state criterion).** `S` is unchanged by a modification of reading `y` iff, at every `R_i` (i < n), the largest exit among blockers is still `R_{i+1}` and `R_n` is still clear. Induction on `i`. Everything below is a case of this criterion.

## Summary

| # | Transformation | Preserves (exact condition) | Fails when |
|---|---|---|---|
| 1 | `rho_y -> rho_y + 8m` | `S, I, L, O`: if `y` and `y' = rho_y + 8m` are both clear at every state of `S` (21,781 of 21,781). Block STATUS at integer `R` (33,586 of 33,586), never the jump | `y'` blocks at a state of `S` (2,505 trials: `S` kept in 629) or `y` blocks (9,300 trials: `S` kept in 2,892) |
| 2 | `rho_y` moved inside its inert component | `S, I, L, O, P` always (47,391 of 47,391); `C` iff the rule in 2 below | outside the component: `S` kept in 293 of 15,282 |
| 3 | `rho_y -> rho_y + 8k/R*` | position at `R*` (37,056 of 37,056); `S, I, L, O` if `y`, `v` both clear at `R_0..R_{n-1}` (21,213 of 21,213) | `y` or `v` blocks earlier: `S` kept in 10,205 of 15,843 |
| 4 | `rho -> lam*rho` | exact: states scale by `1/lam` (10,000 of 10,000). Fixed start `R' = 1`: `L = R*` iff `lam <= R*` (0 violations in 8,400 starts) | `lam > R*`: landing is `first unblocked >= lam` |
| 5 | `rho -> 2c - rho` | block status at `R` iff `2cR in 8Z` (8,000 of 8,000); never the exit | `S` kept in 1,325 of 7,726 when status differs at some state; in 1,279 of 2,657 when status agrees at all states |
| 6 | exchange two readings' values | identity on the state sequence (all 10,500 trials, any pair) | labels only: closer tie at equal entries (2 of 10,500) |

## 1. `rho_y -> rho_y + 8m` (y of rank 2..7, m in {1,2,3,-1}; 33,586 trials on 3,500 arrangements)

Position of `y'` at `R` is `R rho_y + 8mR`: equal to `y`'s mod 8 iff `mR in Z`. Block status at `R_0 = 1`: equal in 33,586 of 33,586. But the exit differs even where status agrees: `y` at lap `j` exits at `(8j+1)/rho_y`, `y'` at lap `j + mR` exits at `(8(j+mR)+1)/(rho_y+8m)`, unequal for `m != 0`. So the statement of log entry 5 (integer `R`: status only) holds, and the jump is not preserved.

Classes (trials n; `S` / `I` / `L` / `O` equal; `P` = rank-labelled path):

| class | n | S | I | L | O | P | C (rank labelled) / C (identity) |
|---|---|---|---|---|---|---|---|
| `y` inert, `y'` clear at all states of `S` | 21,781 | 21,781 | 21,781 | 21,781 | 21,781 (identity) | 16,644 | 5,078 / 9,863 |
| `y` inert, `y'` blocks at some state | 2,505 | 629 | 629 | 644 | 644 | 95 | 316 / 906 |
| `y` blocks, `y'` clear at all states | 1,361 | 432 | 432 | 460 | 458 | 102 | 206 / 265 |
| `y` blocks, `y'` blocks | 7,939 | 2,460 | 2,458 | 3,194 | 3,204 | 2,816 | 1,754 / 2,088 |

- **Condition (exact, 0 violations in 21,781):** `y` and `y'` both inert at `S` implies `S, I, L, O` unchanged. `P` and rank-labelled `C` are not preserved there (16,644 of 21,781) because `y'` is a different value and changes the sorted rank of every reading it passes; identity labels are preserved.
- **Closer rule (0 violations in 9,855 + 390 + 240 + 77 predicted cases):** if `S` is unchanged, `y` is not the original closer, and `y'` has next entry after `R*` strictly greater than `E`, then the closer is unchanged. Closer changed in 11,918 of the 21,781 first-class trials because `y'` has an earlier entry.
- **Landing-only merges:** `L` equal while `S` differs: 15 + 28 + 734 = 777 trials (734 in the last class).
- **Counterexamples (smallest by max denominator, then size):**
  - `y` blocks, `y'` blocks: `rho = [1, 3, 7, 8, 9, 12, 13]`, `rho_3 = 7 -> 15`: states `1, 9/8, 9/7, 17/12` (path `(4,1),(3,1),(6,2)`) become `1, 9/8, 17/15` (path `(3,1),(7,2)`). The blocker `7` at `R = 9/8` exits at `9/7`; `15` exits at `17/15`.
  - `y` inert, `y'` blocks: `[1, 3, 4, 6, 8, 22, 27]`, `rho_4 = 6 -> 14`: `1, 9/8, 25/22` becomes `1, 9/8, 17/14, 11/9` (14 is a lap-2 blocker at `9/8`: `9/8*14 = 15.75`).
  - `y` blocks, `y'` clear: `[1, 3, 7, 8, 9, 12, 13]`, `rho_6 = 12 -> 4`: the last state `17/12` becomes `17/13`.
  - AP `1..7`, `rho_7 = 7+8m`: `R = 1` is lonely for `m = 0..3`: `S` and `L` equal; closer `(7,1), (7,2), (7,3), (7,4)` (entry moves with the lap).
- What the failing cases share: `y` or `y'` is a blocker at some state of `S`. No failure in the both-inert class.

## 2. `rho_y` moved within its inert interval (15,282 inert readings; 47,391 inside points, 15,282 just-outside points)

Inert component of `rho_y`: for each state `R_i` the clear set of `v` is `union_k [(8k+1)/R_i, (8k+7)/R_i]`; with `k_i = floor((R_i rho_y - 1)/8)`,
`[lo, hi] = [max(1, max_i (8k_i+1)/R_i), min_i (8k_i+7)/R_i]`. The component of the intersection through `rho_y` is the intersection of the one interval per state through `rho_y` (components of each union are disjoint closed intervals).

- Inside `[lo, hi]` (endpoints and random interior points): `S, I, L, O` equal in 47,391 of 47,391; rank-labelled path `P` equal in 47,391 of 47,391 although the rank of `y` changed in 26,675 (it never passes a blocker's value: a value equal to a blocker's blocks at the same state, so the component contains none).
- Closer: equal in 27,183 of 47,391. Failures by point type: `hi` endpoint 11,270, interior 8,312, `lo` endpoint 626. Rule as in 1 (y not the original closer and `y'` entry after `R*` > `E`): 21,411 predicted, 21,411 equal; 5,772 closer-equal cases fall outside the rule (closer unchanged although the rule's premise is not met; the premise is sufficient, not necessary).
- Smallest closer counterexample: `[1, 2, 7, 9, 11, 15, 16]`, `rho_2 = 2 -> 49/9` (the `hi` end, `R*` = 9/7): `y'` has entry `7/(49/9) = 9/7 = R*`, a zero-width window, closer `(4,2)` entry `15/11` becomes `y'` entry `9/7`.
- Just outside (`hi` + a thousandth of the width): `S` equal in 293 of 15,282 (the 293 where another clear interval of the same state set starts immediately).
- Exact statement: moving an inert reading inside its component preserves the path and landing; it changes the closer exactly when it brings `y`'s next entry after `R*` to or below `E`.

## 3. `rho_y -> rho_y + 8k/R*` (same residue class modulo `8/R*`; y rank >= 2, k in +-1..3; 37,056 trials)

Position at `R*` equal in 37,056 of 37,056 (`R* v = R* rho_y + 8k`). Earlier states are not protected, so the condition is on `R_0..R_{n-1}`:

| class | n | S | I | L | O | C |
|---|---|---|---|---|---|---|
| `y`, `v` clear at all earlier states | 21,213 | 21,213 | 21,213 | 21,213 | 21,213 | 9,775 |
| `y` clear earlier, `v` blocks earlier | 4,031 | 3,726 | 3,726 | 4,031 | 4,031 | 2,279 |
| `y` blocks earlier, `v` clear earlier | 5,431 | 2,781 | 2,780 | 3,458 | 2,958 | 1,537 |
| `y` blocks earlier, `v` blocks earlier | 6,381 | 3,698 | 1,825 | 4,633 | 2,530 | 2,324 |

- Exact condition (0 violations): both clear at `R_0..R_{n-1}` gives `S, I, L, O`; closer by the rule of 1 (9,770 predicted, 9,770 equal; 2,024 of 2,024; 1,170 of 1,170; 1,725 of 1,725).
- `L` and `O` equal in all 4,031 trials of the class `y` clear earlier, `v` blocks earlier, with `S` differing in 305: the paths diverge and merge at `R*` (observed: the paths diverge and rejoin before `R*`).
- Counterexamples: `[1, 2, 5, 7, 8, 12, 19]`, `rho_3 = 5 -> 85/9` (k=1, `R* = 9/5`): the final jump `17/12 -> 9/5` disappears (`v` is clear at `17/12`), landing `17/12`. Landing-only: `[1, 2, 6, 10, 15, 24, 27]`, `rho_2 = 2 -> 394/17`: `1, 25/24, 17/15` becomes `1, 425/394, 17/15`. First landing failure: `[1, 3, 8, 25, 30, 38, 39]`, `rho_3 = 8 -> 200/9` (k=2, `R* = 9/8`): `1, 9/8` becomes `1`.
- Closer is not preserved by the residue condition: position at `R*` is equal but the speed differs, so the entry differs.

## 4. Uniform scaling `rho -> lam*rho`

- **Part A (exact).** `path` starts at `1/min`. With `rhos' = lam*rhos`: blocking at `R'` is `R' lam rho`, so `R_i' = R_i/lam` and the path is identical. 10,000 of 10,000 (states `R_i'*lam = R_i`, identity path equal; normalised outcome `path` and `R*` equal).
- **Part B (the start is fixed at `R' = 1`).** The raw cascade on `lam*rho` from `R' = 1` equals the cascade of `rho` from `R = lam`. By F1 its landing is the first unblocked `R >= lam`.
  - **Exact: `L = R*` iff `lam <= R*`.** For `lam <= 1`: `(0,1)` is covered by reading 1's `j = 0` zone, so no unblocked point lies in `[lam, 1)`. For `1 <= lam <= R*`: `R*` is the first unblocked point `>= 1`, so `[1, R*)` is blocked. For `lam > R*`: the landing is `>= lam > R*`. 0 violations in 8,400 starts (`s` in {1/3, 1, midpoint, `R*`, `R*+1/100`, `R*+1`, random}: equal and `s <= R*` in 4,832; unequal and `s > R*` in 3,568); and 12,000 trials with `lam` in (0,1) incl. targeted readings inside `(8j-1,8j+1)/lam`: 0 landings differ.
  - The state sequence is not preserved for `lam != 1`: chain from `lam` is a suffix of the chain from 1 only if `lam` is a state (per 2,500 arrangements: 3 of `lam = 11/10`, 85 of `3/2`, 1 of 2, 10 of 3).
  - `lam` row table in `equiv_t4_v1.out` (landing equal: 2,500 at `lam <= 1`; 998, 543, 179, 36, 10, 1, 0 at `11/10, 5/4, 3/2, 2, 3, 5, 7`; zero from 8 up).
  - Counterexample: `[1, 2, 5, 10, 13, 17, 24]`, `R* = 25/24` (at `R = 1` reading 24 sits at position 0 and blocks, exit `25/24`); `lam = 11/10`: lonely at once, landing `11/10`.
- So scaling is an exact symmetry of the cascade in `R/lam`; it fails to be one for a fixed start at 1 exactly when `lam` is above the landing.

## 5. Reflection `rho -> v = 2c - rho`

`R v = 2cR - R rho`; the blocked set `(-1,1) + 8Z` is symmetric, so status(v at R) = status(rho at R) for all `rho` iff `2cR in 8Z` (the blocked set equals its reflection about `t/2` only for `t` in `8Z`; with `2cR` not in `8Z` status differed for some `rho` in 3,041 of the 7,975 generic trials below).
- `v = 16m/R_0 - rho` (mirror about a multiple of `8/R_0`): status at `R_0` equal in 8,000 of 8,000; at `R' = n R_0/(2m)` equal in 8,000 of 8,000; at generic `R'` equal in 4,934 of 7,975 (differs in 3,041).
- `v = 8k - rho`: status at `R in Z/k` equal in 8,000 of 8,000; at `R_0 = 1` equal in 32,724 of 32,724 cascade trials.
- **The exit is not preserved.** The mirrored runner is at the mirrored position but moves forward: its exit is at position `+1` of its own motion, not the original's entry. Part C: reflecting a blocker of `R_0` about `8m/R_0` keeps the jump `R_0 -> R_1` in 2,131 of 6,182 trials. Example: `[1, 267/200, 3, 4, 4913/1000, 5, 807/100]`, `rho_7 -> 793/100`: `R_1 = 300/269` becomes `900/793`.
- Cascade with `rho_y -> 8k - rho_y` (32,724 trials): both `y`, `v` clear at all states of `S`: `S, I, L, O` equal in 22,341 of 22,341 (this is the both-inert condition of 1; reflection adds nothing there). Status equal at every state but one of them blocks: `S` equal in 1,279 of 2,657. Status differing at some state: 1,325 of 7,726.
- Counterexamples: `[1, 3, 8, 9, 10, 19, 28]`, `rho_2 = 3 -> 21` (k=3; status differs): last state `33/28` becomes `25/21`; `rho_3 = 8 -> 16` (k=3; status agrees at every state of `S`): `1, 9/8, 33/28` becomes `1, 17/16`. In the second, `8` and `16` both block `R = 1` (status agrees) but exit at `9/8` and `17/16`.
- What fails shares: `y` or `v` is a blocker at some state of `S`.

## 6. Exchange of two readings' values

The cascade reads the multiset: `blocks` and the exit of reading `i` depend on `rho_i` only, and the largest exit is taken over the multiset. So the state sequence is unchanged for every pair.
- 10,500 trials (3,500 shuffled tuples, 3 pairs each): `S` equal 10,500; `L` equal 10,500; identity path equals the original with the two positions exchanged 10,500; sorted-rank `(rank, lap)` path and sorted `(opener, closer)` equal 10,500.
- By condition: both readings clear at every state 6,777; never both blocking 3,054; both blocking at a common state 669: 0 failures in each. The disjointness condition is therefore not needed.
- Only label changes: closer identity with exchanged positions equal in 10,498 of 10,500; the two exceptions are ties at a zero-width window: `[3, 28, 7, 23, 27, 9, 1]` (lonely at `R = 1`), positions 3 and 0 exchanged, entries `(24-1)/23 = 7/7 = 1`, closer label `(2,1)` becomes `(0,3)`. This is log entry X7's mechanism (equal values of the argmax broken by position).

## 7. Equivalence classes by path

### Tree cells (`terminals5_J1.pkl`, 9,652 cells)
- Distinct paths 6,706. Cells in paths shared by at least two cells: 4,829 in 1,883 families (sizes 2: 1,414; 3: 219; 4: 137; 5: 35; 6: 27; 7: 17; 8: 10; 9: 9; 10: 7; 11: 3; 12: 1; 14: 3; 22: 1). Singletons 4,823.
- Openers (last step): 40 distinct; largest `(7,9)` 1,821 cells in 796 paths, `(5,4)` 754 in 615, `(5,6)` 723 in 475, `(6,8)` 688 in 472, `(7,6)` 565 in 454.
- Same path, 5,659 pairs: 1,147 with at least one of ranks 2..7 having disjoint ranges; **52 pairs with all six ranges disjoint** (arrangements that look different in every reading and share a path), in 24 of 1,883 families. Greedy mutually-all-disjoint subsets have size at most 2.
- Same opener, all six ranges disjoint: 635,458 pairs of the 1,657,110 in `(7,9)` (635,433 with different paths); 26,958 in `(5,4)`; 111,080 in `(5,6)`; 104,093 in `(6,8)`.
- 79 identical seven-range boxes carry two or more different paths.
- Cell path is the label stored with the cell: the witness's own `outcome` path equals it in 6,589 of 9,652 (the other 3,063: the witness sits on a boundary, readings at 9.0).
- Ten largest path-families containing an all-six-disjoint pair (cells; pairs; pairs with at least one disjoint rank; pairs with all six; path length; last step): (10; 45; 20; 4; 21; (7,9)), (9; 36; 21; 2; 21; (7,9)), (8; 28; 12; 3; 22; (7,9)), (8; 28; 13; 1; 21; (7,9)), (8; 28; 13; 1; 21; (7,9)), (8; 28; 16; 5; 21; (7,9)), (7; 21; 6; 5; 23; (4,6)), (7; 21; 5; 1; 21; (5,6)), (7; 21; 14; 5; 21; (5,6)), (6; 15; 8; 2; 21; (4,5)). Full paths and example pairs in `equiv_classes_v1.out`. Example: path ending `...(2,3),(7,9)`, cells 6240 and 6249: rank ranges `(2.556,2.584), (3.407,3.444), (4.105,4.306), (4.652,4.712), (5.769,5.918), (7.258,7.338)` versus `(2.664,2.679), (3.557,3.571), (4.369,4.465), (4.858,4.885), (6.111,6.136), (7.4..)`.
- Largest path-families regardless of disjointness: (22 cells, path length 22), (14, 22), (14, 23), (14, 22), (12, 21), (11, 22), (11, 21), (11, 22), (10, 21), (10, 22).

### Survey arrangements (`outcome_survey_v2.pkl`, 20,000)
- By path: 1,413 classes (938 singletons; 19,062 arrangements in classes of size at least 2; largest 7,307 = the empty path, lonely at `R = 1`; then 863, 797, 764, 724, 702). By opener: 109 classes. By (opener, closer): 1,083. By lap vector at the landing: 1,919.
- Path families with at least two members: 475; with a pair whose six readings (ranks 2..7) all differ by at least 1/4 / 1/2 / 1 / 2: 356 / 318 / 275 / 236. Opener families (95): 93 / 91 / 91 / 89. (opener, closer) families (565): 507 / 469 / 414 / 348.
- Ten largest path families (members, key, largest min-over-ranks difference between two members): 7,307 `()` 69.2; 863 `((5,1),)` 16.1; 797 `((4,1),)` 15.8; 764 `((6,1),)` 14.1; 724 `((3,1),)` 23.6; 702 `((7,1),)` 11.0; 651 `((2,1),)` 34.9; 485 `((6,2),)` 15.8; 390 `((5,2),)` 9.4; 363 `((7,1),(6,1))` 10.2. Example in the first non-empty: `[553/500, 319/200, 689/250, 877/100, 9867/1000, 2967/250]` and `[4313/250, 18039/1000, 18989/1000, 3636/125, 14977/500, 30991/1000]` (ranks 2..7, units of `d_min`) share path `((5,1),)`; every reading differs by at least 16.1.
- Ten largest opener families: 7,307 (no opener), 1,386 `(5,1)`, 1,282 `(4,1)`, 1,131 `(6,1)`, 1,063 `(3,1)`, 835 `(2,1)`, 702 `(6,2)`, 702 `(7,1)`, 595 `(5,2)`, 469 `(6,3)`. Largest (opener, closer): 4,550 `(None,(7,1))`, 854, 674, 651, 459, 456, 326, 314, 283, 270.
- Sample composition: members of one path family come from several generator families (`fam`) in 273 of 1,413 path classes.

## Scope notes
- Counts are trial counts in the pools named; the survey and cells are those two files. Rows with 0 violations are runs that would have found a violation had one occurred among those trials; nothing is claimed outside them.
- `rho_y -> rho_y + 8m` on rank 1 (the smallest) was not run (it changes the unit); the pool for the others excludes trials where the minimum changes.
- Part 4's exact criterion (`lam <= R*`) rests on F1; F1 is checked against an independent sweep (8,400 of 8,400) and by the argument stated there.
