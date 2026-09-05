# Resource-Count Reduction on the `(9,1)` Branch
## First symbolic closure of the shell-inequality program — 2026-04-24

---

## Purpose

The `(9,1)` shell-reduction note showed that once the inequalities

- `A >= q`
- `B >= q`
- `C >= q`
- `D > q`

hold for an inner-symmetric count vector

`[z, A, B, C, D, D, C, B, A, z+q]`,

the fixed point is automatically of `E`-type.

This note gives the first genuinely symbolic piece of that program:

1. a clean proof of the first inequality `A >= q`,
2. exact wrong-block formulas showing how the remaining failures would
   contradict self-consistency under the natural partial hypotheses.

So the shell-inequality problem is no longer a single opaque obstacle. It has
been broken into explicit contradiction patterns.

---

## Setup

Assume:

- the fixed point has lead/tail pair `(9,1)`,
- by the inner-asymmetry lemma its counts are

  `[z, A, B, C, D, D, C, B, A, z+q]`,

  with `z >= 1`, `q >= 0`,
- its actual gap profile is the greedy shell pairing of the sorted digits

  `9^(z+q) 8^A 7^B 6^C 5^D 4^D 3^C 2^B 1^A 0^z`.

Let `p_v` denote the multiplicity of the gap value `v` in that actual profile.

For any profile with lead/tail pair `(9,1)`, the borrow reconstruction formulas
give:

- `c1 = p8 + p1`
- `c2 = p7 + p2`
- `c3 = p6 + p3`
- `c4 = p5 + p4`.

These are just the specializations of the standard tail-`1` block count map.

---

## Theorem A — the first shell inequality `A >= q`

After the `z` outer `9-0` shell pairs are exhausted, there remain exactly
`q = c9-c0` unmatched `9`s on the top half.

Suppose for contradiction that `A < q`.

Then:

- every one of the `A` copies of digit `1` is forced to pair with one of those
  unmatched `9`s,
- so the actual gap profile has exactly

  `p8 = A`

  copies of the gap `8`,
- and because the overall lead/tail pair is `(9,1)`, the actual profile has at
  least one gap `1`:

  `p1 >= 1`.

Therefore the reconstructed count of digit `1` is

`c1 = p8 + p1 >= A + 1`,

but the original count vector has

`c1 = A`.

Contradiction.

So:

> every fixed point on the `(9,1)` branch satisfies `A >= q`.

This is the first clean resource-count inequality.

---

## Wrong-block formula for `B < q`

Assume now:

- `A >= q`
- `C >= q`
- `D > q`

and suppose for contradiction that

- `B < q`.

Then the greedy shell pairing is forced as follows:

1. `z` copies of `9-0`, giving `9^z`
2. `q` copies of `9-1`, giving `8^q`
3. `A-q` copies of `8-1`, giving `7^(A-q)`
4. `B` copies of `8-2`, giving `6^B`
5. `q-B` copies of `8-3`, giving `5^(q-B)`
6. `B` copies of `7-3`, giving `4^B`
7. `C-q` copies of `6-3`, giving `3^(C-q)`
8. `q` copies of `6-4`, giving `2^q`
9. `D-q` copies of `5-4`, giving `1^(D-q)`.

So the actual gap profile is exactly

`g = (9^z, 8^q, 7^(A-q), 6^B, 5^(q-B), 4^B, 3^(C-q), 2^q, 1^(D-q), 0^u)`.

Reconstructing counts from this gap profile gives:

- `c1' = p8 + p1 = q + (D-q) = D`
- `c2' = p7 + p2 = (A-q) + q = A`
- `c3' = p6 + p3 = B + (C-q) = B + C - q`
- `c4' = p5 + p4 = (q-B) + B = q`.

For self-consistency we would need

- `c2' = B`
- `c3' = C`
- `c4' = D`.

But already

- `c3' = B + C - q < C`

since `B < q`.

Contradiction.

So under the natural outer hypotheses `A>=q, C>=q, D>q`, the branch `B<q`
cannot occur.

---

## Wrong-block formula for `C < q`

Assume:

- `A >= q`
- `B >= q`
- `D > q`

and suppose for contradiction that

- `C < q`.

Then the greedy shell pairing is forced as follows:

1. `z` copies of `9-0`, giving `9^z`
2. `q` copies of `9-1`, giving `8^q`
3. `A-q` copies of `8-1`, giving `7^(A-q)`
4. `q` copies of `8-2`, giving `6^q`
5. `B-q` copies of `7-2`, giving `5^(B-q)`
6. `C` copies of `7-3`, giving `4^C`
7. `q-C` copies of `7-4`, giving `3^(q-C)`
8. `C` copies of `6-4`, giving `2^C`
9. `D-q` copies of `5-4`, giving `1^(D-q)`.

So the actual gap profile is exactly

`g = (9^z, 8^q, 7^(A-q), 6^q, 5^(B-q), 4^C, 3^(q-C), 2^C, 1^(D-q), 0^u)`.

Reconstructing counts from this gap profile gives:

- `c1' = p8 + p1 = q + (D-q) = D`
- `c2' = p7 + p2 = (A-q) + C`
- `c3' = p6 + p3 = q + (q-C) = 2q - C`
- `c4' = p5 + p4 = (B-q) + C`.

But self-consistency would require `c3' = C`, i.e.

`2q - C = C`,

so `C = q`, contradicting `C < q`.

Therefore under `A>=q, B>=q, D>q`, the branch `C<q` is impossible.

---

## Wrong-block consequence for `D <= q`

Assume:

- `A >= q`
- `B >= q`
- `C >= q`

and suppose

- `D <= q`.

Then after the first forced `q` layers

- `9-1`
- `8-2`
- `7-3`
- `6-4`

there is no `4` left to pair with `5`.

So no gap `1` can appear.

But the branch hypothesis is `beta = 1`.

Contradiction.

So under `A>=q, B>=q, C>=q`, one must have `D > q`.

---

## What is now reduced

This note proves `A >= q` cleanly and makes the remaining three shell
inequalities explicit contradiction targets.

The endgame is now:

1. `A >= q` — proved here
2. `B >= q` — reduced to the `B<q` wrong-block contradiction
3. `C >= q` — reduced to the `C<q` wrong-block contradiction
4. `D > q` — reduced to the no-`1` contradiction once `B,C` are in place

So the shell-inequality program is no longer one amorphous claim.
It has become a short chain of concrete resource contradictions.

---

## Computational alignment

The full-corpus sweep already checked both endgame claims on all available
base-10 fixed-point rows through `d<=1000`:

- rows scanned: `9,910,464`
- bad lead/tail pair count: `0`
- `(9,1)` shell-inequality failures: `0`

So the reductions above are aligned with the entire current corpus.

See:

- [global_promotion_sweep_2026-04-23.md](/Users/trentpalelei/Desktop/Kaprekar/analysis/base10/global_promotion_sweep_2026-04-23.md)
- [e_branch_shell_reduction_2026-04-23.md](/Users/trentpalelei/Desktop/Kaprekar/analysis/base10/e_branch_shell_reduction_2026-04-23.md)
