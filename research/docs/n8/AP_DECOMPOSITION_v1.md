# Splitting a runner's difference set into an AP part and a residual

2026-09-13. n = 8, individual isolation, threshold 1/8. Follows the owner's question: in a
configuration the grid reference cannot reach, can the locally-AP portion still be treated as an
AP?

Answer: yes, and it gives an exact decomposition of the problem.

---

## 1. The decomposition  `[PROVED — arithmetic]`

For runner `i` with `m = d_min(i)`, partition its seven differences:

| part | definition | test | language |
|---|---|---|---|
| `D_div` | `m │ d` | blocks iff `d ≡ 0 mod 8m` | **residues** — AP / grid |
| `D_non` | `m ∤ d` | blocks iff `dist(d/m, 8ℤ) < 1` | band test only |

The runner attains `1/(8m)` iff **neither** part blocks. On `D_div`, `s = d/m` is an integer, so
`dist(s, 8ℤ) < 1` collapses to `s ≡ 0 mod 8` — the grid criterion, exactly.

`GRID_REFERENCE_REACH_v1`'s theorem is the special case `D_non = ∅`.

## 2. Worked on the adversarial example

`V = (1, 3, 5, 9, 12, 14, 16, 18)` — no two speeds adjacent, the reference reaches no runner,
floor 4. Its local APs are `(1,3,5)` and `(12,14,16,18)`, both of step 2.

| runner | `d_min` | `D_div` | `D_non` | what blocks |
|---|---|---|---|---|
| r1 | 2 | `2, 4, 8` | `11, 13, 15, 17` | **15, 17** (non-div) |
| r2 | 2 | `2, 2, 6` | `9, 11, 13, 15` | **15** (non-div) |
| r3 | 2 | `4, 2, 4` | `7, 9, 11, 13` | — |
| r4 | 3 | `6, 3, 9` | `8, 4, 5, 7` | — |
| r7 | 2 | `4, 2, 2` | `15, 13, 11, 7` | **15** (non-div) |
| r8 | 2 | `6, 4, 2` | `17, 15, 13, 9` | **17, 15** (non-div) |

**Every block comes from `D_non`.** The AP-commensurate part — which is exactly the local AP
structure `(1,3,5)` and `(12,14,16,18)` — never blocks anything here. Treating those triples and
quadruples as APs is correct and costs nothing; what breaks the runners is their relation to the
*other* block, at distances not divisible by 2.

## 3. How the blocking splits in general  `[VERIFIED]`

Over 24,517 runner-instances where the grid reference fails, of which 10,204 are blocked:

| blocking differences | count | share |
|---|---|---|
| in `D_div` — **residue language reaches these** | 3,187 | 0.22 |
| in `D_non` — band test only | **11,103** | **0.78** |

So the AP treatment accounts for about a fifth of the blocking even in configurations it cannot
fully reach, and the remaining four fifths sit in `D_non`.

## 4. What this sharpens

The open problem is now stated on a smaller object. It is not about configurations, or about
grids, or about measure. It is about **`D_non`**: the differences of a runner that are not
multiples of its own smallest gap, and whether `d/m` can land within 1 of a multiple of 8.

| | |
|---|---|
| `D_non = ∅` | the grid theorem applies — proved, nothing blocks unless residues collide |
| `D_non ≠ ∅` | residues say nothing; the band test decides, and this is where 78% of blocking lives |

Three earlier routes reached the same wall — the union bound failing by `3/2`, grid density not
transferring because the moment jumps `5×` at the AP, and the reference stopping where blocking
begins. This names the object they all stop at.

## 5. Status

`[PROVED — arithmetic]` §1's decomposition and the collapse of `D_div` to residues.
`[VERIFIED — exact]` §2's table.
`[VERIFIED — 24,517 instances]` §3's split.

**Not established.** Anything about `D_non`. Whether `dist(d/m, 8ℤ)` admits a bound in terms of
the configuration — a Diophantine question, and the same one left open by
`ANALYTIC_STATUS_v1` §2.

**n = 8 is not proved here.**
