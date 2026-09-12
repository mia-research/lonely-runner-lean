# Working note — the m=16 parity lemma, and moduli along transits

2026-09-12. n=8 only.

## 1. Where this sits

The programme treats every speed set as (permutation, deviation) from an AP/grid
reference: `u_i = π(i) + 8·q_i`. The chain is

1. every arrangement is a permutation/deviation off AP or grid — coordinates established;
2. every runner's transit between neighbouring speeds is mapped;
3. hence no runner fails to be lonely.

Link 3 follows from link 2 once the floor on link 2 is proved rather than sampled.
This note adds one proved step inside link 2, and measures how far the rest is from
being finite.

## 2. The criterion being extended

Proved earlier: for any `m ≤ 8`, runner `i` is lonely at `t = a/m` iff its residue
mod `m` is unique among the eight. This settles 88.6% of runner-instances over
`[1..22]`. The residual is the set of runners that share a residue at *every*
`m ∈ {2,…,8}`.

## 3. The m = 16 parity lemma  [PROVED]

At `m = 16` the loneliness band is `‖x‖ ≥ 1/8`, i.e. the residue of `e_j·a` mod 16
must lie in `[2,14]`. So exactly three residues are forbidden: `0, +1, -1`.

- `e_j·a ≡ 0 (mod 16)` with `a` a unit requires `16 | e_j`.
- `e_j·a ≡ ±1 (mod 16)` requires `e_j` odd, and then `a ≡ ±e_j^{-1}`, which is
  **exactly two** of the eight units mod 16.
- `e_j` even and not divisible by 16 forbids nothing: `e_j·a` is even and nonzero.

Hence

> **Lemma.** If runner `i` has at most 3 odd differences and none divisible by 16,
> then at most `2·3 = 6` of the 8 units mod 16 are forbidden, so at least two
> survive and `t = a/16` is a witness.

"At most 3 odd differences" means at most 3 of the other seven runners have the
opposite parity — i.e. **runner `i`'s parity class has at least 5 members.**
This is a condition on `π` alone; the deviations `q_i` do not enter.

An 8-set splits into parity classes as 8-0, 7-1, 6-2, 5-3 or 4-4. In every split
except 4-4 the majority class has ≥ 5 members, so **every runner in the majority
parity class is lonely at a sixteenth**, subject to the `16 ∤ e_j` side condition.

Check over `[1..24]`: 1,917,000 qualifying runner-instances, **0** with fewer than
two survivors.

## 4. Coverage  [MEASURED, range [1..22]]

| stage | settles | in permutation terms |
|---|---|---|
| `m ≤ 8` uniqueness | 88.6% of 2,556,840 | unique grid point at some `m ≤ 8` |
| `m = 16` parity lemma | 118,514 = 40.75% of the 290,800 residual | majority parity class |
| remainder | 172,286 | — |

Of the remainder, 57,926 still have a surviving unit at `m = 16` (the lemma's
sufficient condition is not necessary); 114,360 have none. Every one of those
114,360 is covered by some modulus in `[9, 23]` — first-hit distribution

`9:16974  10:16842  11:42572  12:7604  13:18430  14:5930  15:3396  17:146
 18:222  19:1124  20:582  21:292  22:102  23:144`

with **zero** uncovered up to 96.

The leftover, broken down by number of odd differences:

`0:226  1:5906  2:23652  3:37692  4:84650  5:20160`

The `nodd ∈ {0,1,2,3}` entries are there only because of the `16 | e_j` side
condition. The dominant block is `nodd = 4` — **the arrangements that survive both
criteria are the parity-balanced ones**, four even and four odd.

## 5. Moduli along transits  [MEASURED]

For each integer position of the sliding speed, `mmin(V,i)` = least `m ≤ 200` with
a surviving unit; the table reports `max_i mmin(V,i)`.

| transit | max modulus on the transit | failures |
|---|---|---|
| AP `(1..8)`, slide r1 from 1 to 2 | 8 | 0 |
| AP `(1..8)`, slide r8 from 8 to 40 | 19 | 0 |
| E* `(0,2,6,7,8,10,13,14)`, slide r1 from 0 to 2 | 15 | 0 |
| E*, slide r8 from 14 to 40 | 15 | 0 |

The modulus does not grow with distance. AP sliding r8 rises to 19 at `v = 17,18`
and falls back to 12–13 by `v = 33..38`. E* sliding r8 is flat at 14 from `v = 15`
through `v = 40`, with 15 at `v = 14, 21, 28`.

## 6. Status

- §3 is a proof. It is a statement about `π` and holds for all deviations.
- §4 and §5 are measurements over the stated ranges.
- The bounded-modulus behaviour in §5 is what link 2 needs, and it is not yet proved.
  A proof of "the least witnessing modulus is bounded along every transit" would
  close link 2; a bound on the modulus for parity-balanced arrangements would be
  the natural next target, since §4 isolates those as the only block the two proved
  criteria miss.
