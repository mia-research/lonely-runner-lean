# The tiling, the four blocks, and the parity law — n=8 from `|I| = 1/4`

2026-09-10. Scripts `experiments/n8/ok_blocks_v1.py`, `ok_parity_law_v1.py`,
`ok_odd_room_v1.py`. Exact `Fraction` throughout; every claim below is either derived in
two lines or verified exhaustively in a stated box, and the two are marked apart.

Nothing here is translated from `n = 11` or from any other `n`. It starts from one fact
that is specific to the threshold `1/8`, and follows it.

---

## 0. The fact everything comes from

The bad interval is `I = (−1/8, 1/8)`, of length **exactly `1/4`**. So its four translates
by `1/4` **tile** the circle:

    1_I(θ) + 1_I(θ+1/4) + 1_I(θ+1/2) + 1_I(θ+3/4) = 1     for a.e. θ.

That is an identity, not a bound. Feed it the shift `t ↦ t + 1/8` — which is exactly the
`r`-freedom of the bridge, `T_j = t + j/8` — and runner `e`'s argument moves by `e/8`, of
order `8, 4, 2, 1` in `ℝ/ℤ` according as `v₂(e) = 0, 1, 2, ≥3`. Intersecting each orbit
with `I` and using the tiling gives **exact counts**:

| `v₂(e)` | orbit | `∩ I` | blocked set in `ℤ/8` |
|---|---|---|---|
| 0 | 8 points, spacing `1/8` | **exactly 2** | `{j, j+ρ}`, `ρ = e mod 8` odd — one odd `j`, one even `j` |
| 1 | 4 points, spacing `1/4` | **exactly 1** (the tiling) | `{j, j+4}` — one full block |
| 2 | 2 points, spacing `1/2` | 0 or 1 | a whole parity class, or nothing |
| ≥3 | 1 point | 0 or 1 | all 8, or nothing |

**Verified exactly, 0 shape violations** over 4 000 random `(e, t)` with `e ≤ 400`.

## 1. The right unit is the block, not the residue  `[PROVED]`

`ℤ/8` is four **blocks** — the classes mod 4:

    A = {1,5},  B = {3,7}   (odd)        C = {0,4},  D = {2,6}   (even)

and the table above reads: a `v₂ = 1` runner covers **one whole block**; a `v₂ = 0` runner
covers **one element** of an odd block and **one element** of an even block; `v₂ = 2` covers
two blocks of one parity or none; `v₂ ≥ 3` covers all four or none.

A block has two elements, so **an uncovered block can only be finished by two odd runners.**
Writing `a = #{odd speeds}` and `u_O, u_E` for the numbers of odd/even blocks left uncovered
by the `v₂ ≥ 1` runners at `t`:

> **Block criterion `[PROVED]`.** If `a < 2·max(u_O, u_E)` at some `t`, a witness exists.

No measure appears anywhere in it.

**Verified: the implication held in 20 400 of 20 400 cells** where it fires (400 Case-2
tuples sampled from `[1..16]`, exact cell decomposition at the breakpoints `m/(8e)`).

**Reach, and its exact boundary.** There are only two blocks per parity, so `max(u_O,u_E) ≤ 2`
and the criterion is **provably unreachable for `a ≥ 4`**. Measured on the same sample:

| `a` | tuples | settled |
|---|---|---|
| 1 | 11 | 11 |
| 2 | 59 | 56 |
| 3 | 169 | 162 |
| ≥4 | 161 | **0** — unreachable by construction |

**53% of Case 2 settled with no estimate of any kind**, and the criterion is essentially
coextensive with `a ≤ 3` (229 of 239).

## 2. Two groups on one state  `[PROVED]`

Since `⌊⌊8et⌋/2⌋ = ⌊4et⌋`, put `q_e = ⌊4et⌋ mod 4` (the **quarter state**) and
`β_e = ⌊8et⌋ mod 2` (the extra bit). Then for an odd runner with `ρ = e mod 8`:

    odd element    o_e = −ρ(2q_e + 1)        mod 8     — depends on q_e ALONE
    even element   z_e = −2ρ(q_e + β_e)      mod 8     — needs the extra bit

**Verified 0 mismatches / 6 000 each**, and `block(o_e) = −χ₁(ρ)·(−1)^{q_e}` likewise
(`χ₁(ρ) = ±1` as `ρ ≡ 1, 3 mod 4`). *The sign here was inverted in the first run — 6 000/6 000
mismatches — and is corrected above; the algebra `−ρ·1 ≡ 3 (mod 4)` fixes it.*

The content is the asymmetry. The odd residues `{1,3,5,7}` are the **Klein** group
`(ℤ/8)^*`; the even residues are **cyclic** `ℤ/4` via `z ↦ z/2`. One odd runner must cover
one element of each, and both are driven by the *same* `q_e` — but `q ↦ 2q+1` is **not** a
homomorphism `ℤ/4 → (ℤ/8)^*`. That mismatch is the `2φ(8)/8 = 1` break-even in structural
form rather than as a density identity, and it is what the block criterion runs out of road
against at `a ≥ 4`.

## 3. The parity law  `[PROVED — two lines]`

Let `Bl(t) ⊆ ℤ/8` be the residues blocked at `t`, `O* = {t : {1,3,5,7} ⊆ Bl(t)}`,
`E* = {t : {0,2,4,6} ⊆ Bl(t)}`, `o = |O*|`, `u = |O* ∩ E*|`.

> **`E* = O* − 1/8`, hence `|O*| = |E*|` for every tuple.**

*Proof.* `T_j(t + 1/8) = T_{j+1}(t)`, so `Bl(t+1/8) = Bl(t) − 1`, and subtracting 1 swaps
the odd and even residues. So `t + 1/8 ∈ O* ⟺ {0,2,4,6} ⊆ Bl(t) ⟺ t ∈ E*`. Lebesgue
measure is translation invariant. ∎

**Verified 1715 / 1715**, exhaustive over Case 2 in `[1..14]`. (Disjointness of the two
failure sets is **not** a law — 578/1715, 33% — and is not claimed.)

## 4. What it buys: eight residues down to four  `[PROVED]`

`u ≤ o`, so `o < 1` alone produces a witness. Since `(1−o) + (1−o) ≥ 1−u`,

> **`1 − o ≥ (1−u)/2`** — the four-residue target costs **at most a factor 2** in room, and
> **`o(E) < 1` implies LRC(8) for that tuple.**

Exhaustive over Case 2 in `[1..14]` (1 715 tuples): `min (1−u) = 93/1820` and
`min (1−o) = 93/3640`, **both attained at `(2,6,7,8,10,13,14)`** — the known extremum — and
there the factor is exactly 2, the two sides being equal *and* disjoint. **No tuple has
`1−o = 0`.**

So the Case-2 target `∫X ≥ 93/1820` of `U_REFORMULATION_v2` §3 may be replaced by

> **Odd-side target.** `o(E) < 1` for every 7-tuple with `gcd 1` and a multiple of 8 —
> i.e. some `t` leaves one of the four **odd** residues unblocked.

Four residues instead of eight; the `v₂ ≤ 1` runners enter only through their **quarter**
states, and only the `v₂ ≥ 2` runners still need the `1/8` resolution. It is a strictly
stronger statement on a strictly coarser object, and the strengthening is bounded by 2.

## 5. Grades, and what is not claimed

§0 orbit counts, §1 block table and criterion, §2 identities, §3 parity law, §4 inequality
`1−o ≥ (1−u)/2`: **PROVED**, each verified exactly as stated (0 violations / 20 400 of
20 400 / 0 of 6 000 / 1715 of 1715).
The 53% reach, the `a`-breakdown, and both `min` values: **EMPIRICAL — exhaustive or
sampled in the stated box only**, one-sided as always.

`n = 8` is **not proved**. What changed: the `a ≤ 3` half of Case 2 now closes with no
estimate at all, the obstruction at `a ≥ 4` is named (Klein vs cyclic on a common quarter
state), and the target is four residues rather than eight at a cost of at most a factor 2.
Nothing here uses `LRC(8)`, Rosenfeld, or any `n ≠ 8` machinery.
