# Which configurations achieve global isolation — and the permutation/deviation coordinates

2026-09-12. Script `experiments/n8/ok_which_grids_v1.py`. Exact `Fraction`.
Answers the owner's two questions: *which grids achieve global isolation*, and *treat runners
as permutations/deviations from AP points, no matter the spread*. They turn out to be the same
answer.

---

## 1. The criterion  `[PROVED + VERIFIED exhaustively]`

> Translate so one runner sits at 0; divide by `g`, the gcd of the differences.
> **Global isolation ⟺ the reduced speeds are a complete residue system mod `n`.**
> It then occurs at exactly **`φ(n)`** times, `t = p/(n·g)` with `gcd(p,n) = 1`.

Proof is the five lines of `FRAME_FREE_RESTATEMENT_v1` §1: the gap-sum forces the exact
`n`-grid; `n(v_i−v_j)t ∈ ℤ` forces `t = p/(n·g)`; multiplication by `p` permutes `ℤ/nℤ`.

Checked against a direct evaluation at every admissible time:

| | `n=4`, `[1..16]` | `n=5`, `[1..15]` | `n=6`, `[1..14]` | `n=7`, `[1..14]` |
|---|---|---|---|---|
| sets | 1820 | 3003 | 3003 | 3432 |
| achieve global isolation | 292 (**16.04%**) | 243 (**8.09%**) | 148 (**4.93%**) | 128 (**3.73%**) |
| criterion disagreements | **0** | **0** | **0** | **0** |

## 2. The permutation/deviation coordinates  `[PROVED + VERIFIED]`

Write each reduced speed as

> **`u_i = π(i) + n·q_i`**,  `π(i) = u_i mod n`  (the *permutation part*),  `q_i ∈ ℤ` (the
> *deviation*).

Then **`π` alone decides global isolation, and the `q_i` are invisible to it.** Both
directions verified:

- `π =` identity with random deviations always isolates — `(4,21,25,27,31,38,48,50)`,
  `(1,7,20,29,38,40,43,50)`, `(5,9,11,18,32,38,52,55)`: speeds spread over a range of 50,
  nothing like an AP, all globally isolated.
- `π = (0,0,2,2,5,6,6,7)` — the residue pattern of `E* = (0,2,6,7,8,10,13,14)` — **cannot be
  rescued by any deviation.** Four random `q` vectors, all fail.

So *"no matter the spread, treat runners as permutations/deviations from AP points"* is exactly
right, and the spread genuinely does not matter: it lives entirely in `q`, which global
isolation cannot see. The AP `{0,1,…,n−1}` is simply the representative with `q = 0`.

## 3. At `n = 8`  `[VERIFIED — exhaustive]`

| box | achieve global isolation |
|---|---|
| `[1..16]` | 258 / 12 870 = **2.00%** |
| `[1..20]` | 1304 / 125 970 = **1.04%** |
| `[1..24]` | 6593 / 735 471 = **0.90%** |

Worked examples, all with reduced residues `{0,…,7}`:

| set | `g` | |
|---|---|---|
| `(1,2,3,4,5,6,7,8)` | 1 | the AP |
| `(1,2,3,4,5,6,7,16)` | 1 | not an AP — `16 ≡ 8` |
| `(1,2,3,4,5,6,15,24)` | 1 | two terms displaced |
| `(2,4,6,8,10,12,14,16)` | 2 | AP of step 2 |
| `(1,3,5,7,9,11,13,15)` | 2 | the odd coset |
| `(3,6,9,12,15,18,21,24)` | 3 | AP of step 3 |

`φ(8) = 4`, so each is globally isolated at exactly four instants per period.

## 4. What this separates

- **Global isolation** sees only `π`. The deviations are free, so the class is far larger than
  "AP" — it is *any* complete residue system mod `n`, at any spread.
- **Individual isolation** — what LRC asks — is where the deviations matter, because a runner
  may use a modulus `m ≠ n`, and mod `m` the `q_i` are visible. That is exactly why
  `E*`'s runner 0 needs `m = 15` while its other seven runners are settled at `m ≤ 7`
  (`FRAME_FREE_RESTATEMENT_v1`).

So the permutation part is the whole story for the grid, and the deviation part is the whole
story for the residual difficulty. The two questions decouple cleanly in these coordinates.

## 5. Ledger

`[PROVED]` §1's criterion (derivation in `FRAME_FREE_RESTATEMENT_v1` §1); §2's decomposition.
`[VERIFIED — exhaustive]` §1's four tables, 0 disagreements against direct evaluation across
11 258 sets; §3's three boxes.
`[VERIFIED — exact]` §2's positive and negative examples.
`[SEARCHED, NOT FOUND]` — **not** a novelty claim. `lrc_ap_phi_n_law_v1.md` records the φ(n)
law scoped to "speeds in exact arithmetic progression with common start"; searches for
"complete residue", "residue system", "global isolation", "permutation", "deviation" over
`docs/` and `reports/` surfaced no prior statement dropping the AP hypothesis. Per
`NOVELTY_RETRACTION_v1` §3 that is searched-and-not-found, not established as new.

`n = 8` is **not proved**, and nothing here moves a grade.
