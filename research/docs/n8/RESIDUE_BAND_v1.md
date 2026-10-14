# The residue band — one rule for every arrangement

2026-09-13. n = 8, individual isolation, threshold 1/8. Arbitrary distinct speeds.

Supersedes the framing of `AP_DECOMPOSITION_v1`, `D_NON_EXPLAINED_v1` and the "two scales"
account in `GRID_REFERENCE_REACH_v1` §4 — all of which said residues do not reach non-grid
configurations. **They do.** They need a band instead of a point.

Arrived at from the owner's suggestion: for `(1,3,5,9,12,14,16,18)`, use AP 2.

---

## 1. The theorem  `[PROVED — arithmetic]`

For runner `i`, let `m = d_min(i)` — the smaller of its two adjacent gaps. Then

> **blocked ⟺ `d mod 8m` lies within `m` of `0`**, working in `ℝ / (8m)ℤ`.

For **integer** speeds this is a residue condition in the ordinary sense:

    blocked  ⟺  (d mod 8m)  ∈  {0, 1, …, m−1} ∪ {7m+1, …, 8m−1}

**Proof.** Blocking is `‖d/(8m)‖ < 1/8`. Multiply through by `8m`: the distance from `d` to the
nearest multiple of `8m` is less than `m`. ∎

Verified against the band test on **224,000 of 224,000** differences.

## 2. Worked: AP 2 on `(1,3,5,9,12,14,16,18)`

Lattice step 2 splits the set into cosets — odd `{1,3,5,9}`, even `{12,14,16,18}`. With `m = 2`
the modulus is `8m = 16`:

| partner | 3 | 5 | 9 | 12 | 14 | **16** | **18** |
|---|---|---|---|---|---|---|---|
| `d` | 2 | 4 | 8 | 11 | 13 | **15** | **17** |
| parity | same | same | same | opp. | opp. | **opp.** | **opp.** |
| `d mod 16` | 2 | 4 | 8 | 11 | 13 | **15** | **1** |
| blocks | no | no | no | no | no | **yes** | **yes** |

Same-parity differences are even, so `s = d/2` is an integer and they block at `d ≡ 0 mod 16`.
Opposite-parity differences are odd, so `s` is a half-integer and they block at `d ≡ ±1 mod 16`.
Together: the forbidden residues are `{0, 1, 15}`.

## 3. The special cases

| `m` | modulus `8m` | forbidden residues | count | share |
|---|---|---|---|---|
| **1** | 8 | `{0}` | 1 | **1/8** |
| 2 | 16 | `{0, 1, 15}` | 3 | 3/16 |
| 3 | 24 | `{0, 1, 2, 22, 23}` | 5 | 5/24 |
| `m` | `8m` | `2m−1` residues | `2m−1` | `(2m−1)/(8m)` |
| large | | | | **→ 1/4** |

`m = 1` recovers the grid rule exactly — a single forbidden residue, `0 mod 8`. Every earlier
"grid" result is this line of the table.

**The penalty for leaving the AP is quantitative, not structural.** As a runner's nearest gap
grows from 1, its blocking band widens from `1/8` of residues toward `1/4`. Nothing is lost; the
target doubles.

## 4. What this supersedes

| earlier claim | status |
|---|---|
| "residues have nothing to grip on non-grids" | **wrong** — modulus `8·d_min` reaches them |
| "the grid frame lives on the gcd lattice while the event is at the `d_min` scale" | **wrong** — the frame moves to `d_min` |
| `D_div` / `D_non` as a forced partition | **unnecessary** — one band covers both |
| "make the AP bigger cannot help" | **stands**, but was answering the wrong question: the fix is not a coarser lattice, it is a wider band at the same scale |

## 5. Coverage

| | |
|---|---|
| any distinct real speeds | **yes** — §1 is stated on `ℝ/(8m)ℤ` |
| positive not required | translation-invariant |
| grid / AP structure not required | `m = 1` is just one row of §3 |
| integrality not required | integers give a finite residue ring; reals give the circle |

The blocking test therefore covers **every arrangement**, by proof.

## 6. What is still not proved

Two things, both about what happens *after* blocking:

1. **Where the moment lands when blocked.** The iteration of `MOMENT_ITERATION_v1` finds it
   exactly (9,600 of 9,600, ≤ 11 steps observed) but no step bound is proved.
2. **The first-interval claim** — that the good set meets `[1/(8m), 7/(8m)]`. 21,600 observations,
   no proof, and it implies LRC(8) (`ANALYTIC_STATUS_v1` §3).

So: the **decision** "does this runner attain its bound" is settled for all arrangements. The
**location** of the moment when it does not is settled algorithmically but not analytically.

## 7. Status

`[PROVED — arithmetic]` §1, for all reals.
`[VERIFIED — 224,000 of 224,000]` the residue-band form against the band test.
`[SUPERSEDES]` §4's four framings.

**n = 8 is not proved here.** The band is stated with `8 = n`; whether it reads `nm` for other `n`
is untested.
