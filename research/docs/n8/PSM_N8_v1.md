# The Primary Slot Miss engine, translated to n = 8 — and validated against the source

2026-09-08. Reads the actual mathematics of `lrc_n11_ap_paper_v30.md` §4–§5, not a summary.
Script `experiments/n8/psm_n8_v1.py`, exact `Fraction` throughout. The audit flags eight
`/` sites; every one is `Fraction / Fraction`, hence exact — no float is constructed.

## 1. What PSM is

Paper §5.2, Lemma 5.2. In a completely blocking configuration the **unclaimed slot** must be
covered off schedule; the Coupling Principle (§4.1) says the move is never local, because
runner `j`'s bad intervals are the rigid chain

    B_{j,k}(a_j) = [ (nk + n−1)/(n a_j),  (nk + n+1)/(n a_j) ].

So: if `B_{j,k}` covers the far endpoint `g` of the unclaimed slot, only certain `k` are
feasible given the sign range `a_j ∈ (j−1, j+1)`; each feasible `k` pins `a_j` to a narrow
rational interval; and over that interval `B_{j,0}` lies **entirely outside** some other slot.

**Nothing in this uses primality.** The `11`s are `n`. It is rational interval arithmetic on
the chain formula.

## 2. Validation — the generic code reproduces the paper at n = 11  `[PROVED]`

Run at `n = 11` the same code returns the paper's own constants, case for case:

| paper Lemma 5.2 | its claim | this computation |
|---|---|---|
| Case 1, runner 3 | `a₃ ≤ 230/109`, misses `I₃`, `109/253` vs `43/110` | `a₃ ∈ [2, 230/109]`, misses `I₃`, `109/253` vs `43/110` |
| Case 2, runner 4 | `a₄ ≤ 340/109`, misses `I₂`, `109/374` vs `32/110` | `a₄ ∈ [3, 340/109]`, misses `I₂`, `109/374` vs `16/55` |
| Case 3, runner 5 | `a₅ ≤ 450/109`, misses `I₁`, `109/495` vs `21/110` | `a₅ ∈ [4, 450/109]`, misses `I₁`, `109/495` vs `21/110` |

(`16/55 = 32/110`.) The implementation is therefore checked against the source rather than
against my reading of it.

## 3. The n = 8 table  `[PROVED — exact, exhaustive over all feasible (j,k)]`

`n = 8`, `g = 55/56`, free runners `2..6`, slots `I₁..I₆`, `I_s = [(8s+1)/56, (8s+7)/56]`,
`B_{j,k} = [(8k+7)/(8a_j), (8k+9)/(8a_j)]`.

| `j` | `k` | forced `a_j` range | `B_{j,0}` confined to | slots entirely missed |
|---|---|---|---|---|
| 2 | 0 | `[1, 63/55]` | `[55/72, 9/8]` | 1,2,3,4 |
| 2 | 1 | `[21/11, 119/55]` | `[55/136, 33/56]` | 1,5,6 |
| 2 | 2 | `[161/55, 3]` | `[7/24, 495/1288]` | 1,3,4,5,6 |
| 3 | 1 | `[2, 119/55]` | `[55/136, 9/16]` | 1,**4**,5,6 |
| 3 | 2 | `[161/55, 35/11]` | `[11/40, 495/1288]` | 1,3,**4**,5,6 |
| 3 | 3 | `[217/55, 4]` | `[7/32, 495/1736]` | **2**,3,**4**,5,6 |
| 4 | 2 | `[3, 35/11]` | `[11/40, 3/8]` | 1,3,4,5,6 |
| 4 | 3 | `[217/55, 21/5]` | `[5/24, 495/1736]` | 2,3,4,5,6 |
| 4 | 4 | `[273/55, 5]` | `[7/40, 165/728]` | 2,3,4,5,6 |
| 5 | 3 | `[4, 21/5]` | `[5/24, 9/32]` | **2**,3,**4**,5,6 |
| 5 | 4 | `[273/55, 287/55]` | `[55/328, 165/728]` | **2**,3,**4**,5,6 |
| 5 | 5 | `[329/55, 6]` | `[7/48, 495/2632]` | **2**,3,**4**,5,6 |
| 6 | 4 | `[5, 287/55]` | `[55/328, 9/40]` | 2,3,4,5,6 |
| 6 | 5 | `[329/55, 343/55]` | `[55/392, 495/2632]` | 2,3,4,5,6 |

**Every feasible `(j,k)` forces at least one entire slot to be missed — 0 exceptions**, the
same as at `n = 11` (24 cases there, also 0). The geometric half of PSM translates whole.

## 4. Where the translation genuinely stops, stated exactly

The paper's Case 1 concludes *"no bad interval of runner 3 covers any part of `I₃`, and
`GF(I₃) > 0`"*. That last step needs `I₃` to be **owned** by runner 3 — if the owner misses
its own slot, nothing else covers it. Ownership is Theorem 4.2's pair table.

At `n = 8` the ownership computation (`m_j^± ≡ ±j⁻¹ mod 8`, defined only for `j` invertible)
gives: **runners 3 and 5 form one pair owning `I₂` and `I₄`; runners 2, 4, 6 are not
invertible mod 8 and own nothing; `I₁, I₃, I₅, I₆` are unowned.**

So the table splits cleanly:

- **Runners 3 and 5** — in all six of their feasible cases the missed set contains `I₂` or
  `I₄`, i.e. one of their *own* slots (bolded above). **The paper's inference goes through
  unchanged.**
- **Runners 2, 4 and 6** — own nothing, so a missed slot may still be covered by someone
  else. Their eight cases need the extra step, which at `n = 11` is Chain A, Chain B and
  Universal Blocking (§§5.3–5.5, not yet read).

That is the exact residue: **8 of 14 cases at `n = 8`, all with `j` even.**

## 5. Status

`[PROVED]` the chain/slot instantiation, the n=11 validation, and the n=8 table.
`[NOT CLAIMED]` that the large-ratio case at `n = 8` is closed — six of fourteen cases
inherit the paper's conclusion, eight do not yet. Next: read §§5.3–5.5 and §6 and translate
them for the even, non-owning runners. Nothing here touches Rosenfeld's ledger.
