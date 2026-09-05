# `(9,1)` Resource-Count Closure
## Completing the `E` branch and the global entrance theorem — 2026-04-24

---

## Purpose

The lead/tail theorem has reduced the global promotion step to one branch:

> prove that every `(9,1)` fixed point satisfies the shell inequalities
> `A>=q`, `B>=q`, `C>=q`, `D>q`.

The earlier reduction note already proved `A>=q` and gave the first two
wrong-block contradictions.

This note closes the chain completely.

Together with the earlier shell-reduction note, it finishes the symbolic proof
that the `(9,1)` branch is exactly `E`.

---

## Setup

Let the fixed point have lead/tail pair `(9,1)`.

By inner symmetry its count vector is

`[z, A, B, C, D, D, C, B, A, z+q]`

with

- `z >= 1`
- `q >= 0`.

By the previous resource-count reduction:

- `A >= q`.

So the outer shell pairing is forced to begin with:

1. `z` copies of `9-0`, giving `9^z`
2. `q` copies of `9-1`, giving `8^q`
3. `A-q` copies of `8-1`, giving `7^(A-q)`.

After those forced layers, the remaining shell problem is:

- upper half: `8^q 7^B 6^C 5^D`
- lower half: `2^B 3^C 4^D`.

Also, because the branch tail is `1`, the actual profile has

- `p1 > 0`.

---

## Theorem 1 — `B >= q`

Assume for contradiction that `B < q`.

We split by the size of `C`.

### Case 1. `C >= q`

Then the greedy shell pairing is exactly:

`g = (9^z, 8^q, 7^(A-q), 6^B, 5^(q-B), 4^B, 3^(C-q), 2^q, 1^(D-q), 0^u)`.

This is the wrong-block formula from the earlier reduction note. In
particular:

- `p1 = D-q`,

so the tail condition `p1>0` gives

- `D > q`.

Reconstructing counts gives:

- `c3' = B + C - q`.

Self-consistency requires `c3' = C`, i.e.

`B + C - q = C`,

so `B=q`, contradicting `B<q`.

### Case 2. `C < q` and `B + C >= q`

Now the residual `8`-mass is fully absorbed by the `2/3` layers before the
`4`-layer starts.

The exact shell profile is:

`g = (9^z, 8^q, 7^(A-q), 6^B, 5^(q-B), 4^(B+C-q), 3^(q-C), 2^C, 1^(D-q), 0^u)`.

So:

- `p1 = D-q > 0`,
  hence `D>q`.

Reconstruction gives:

- `c1' = D`
- `c2' = A-q+C`
- `c3' = B+q-C`
- `c4' = C`.

Self-consistency with original counts

- `c1=A`
- `c2=B`
- `c3=C`
- `c4=D`

forces:

- `A = D`
- `C = D`

so

- `A = C = D`.

Then `c2'=B` gives

`B = A-q+C = 2A-q`.

Since `A=D>q`, this yields

`B = 2A-q > q`,

contradicting `B<q`.

### Case 3. `C < q` and `B + C < q`

Now even the combined `2/3` mass does not absorb the residual `8`-layer before
the `4`-layer begins.

The exact shell profile is:

`g = (9^z, 8^q, 7^(A-q), 6^B, 5^C, 4^(q-B-C), 3^B, 2^C, 1^(D-q), 0^u)`.

Again:

- `p1 = D-q > 0`,
  so `D>q`.

Reconstruction gives:

- `c1' = D`
- `c2' = A-q+C`
- `c3' = 2B`
- `c4' = q-B`.

Self-consistency forces:

- `A = D`
- `D = q-B`.

But then

`D = q-B < q`,

contradicting `D>q`.

All cases contradict. Therefore:

> every `(9,1)` fixed point satisfies `B >= q`.

---

## Theorem 2 — `C >= q`

Now assume:

- `A >= q`
- `B >= q`

and suppose for contradiction that

- `C < q`.

Then the greedy shell pairing is exactly:

`g = (9^z, 8^q, 7^(A-q), 6^q, 5^(B-q), 4^C, 3^(q-C), 2^C, 1^(D-q), 0^u)`.

So:

- `p1 = D-q > 0`,
  hence `D>q`.

Reconstruction gives:

- `c3' = q + (q-C) = 2q-C`.

Self-consistency requires `c3' = C`, so

`2q-C = C`,

hence `C=q`, contradicting `C<q`.

Therefore:

> every `(9,1)` fixed point satisfies `C >= q`.

---

## Theorem 3 — `D > q`

Now we know:

- `A >= q`
- `B >= q`
- `C >= q`.

So the shell pairing is exactly the `E` support pattern:

`g = (9^z, 8^q, 7^(A-q), 6^q, 5^(B-q), 4^q, 3^(C-q), 2^q, 1^(D-q), 0^u)`.

Here the tail multiplicity is explicitly:

- `p1 = D-q`.

Since the lead/tail pair is `(9,1)`, we have

- `p1 > 0`.

Therefore:

> every `(9,1)` fixed point satisfies `D > q`.

---

## Shell-inequality theorem for the `(9,1)` branch

Combining the previous reduction with the three theorems above:

> every `(9,1)` fixed point satisfies
>
> - `A >= q`
> - `B >= q`
> - `C >= q`
> - `D > q`.

This is exactly the shell-inequality sublemma left open by the earlier
shell-reduction note.

---

## Corollary — `(9,1)` implies `E`

By the shell-reduction theorem:

- once the shell inequalities hold,
- the shell pairing is forced to have exact `E` support,
- and self-consistency forces `A=B=D`.

So every `(9,1)` fixed point is exactly

`E(z,k,q,d)`

with:

- `k = A-q = B-q = D-q >= 1`
- `d = C-q >= 0`.

Therefore:

> the entire `(9,1)` branch is symbolically equal to the `E` family.

---

## Consequence for the global promotion step

The global entrance theorem is now complete.

We now have:

1. every fixed point has lead/tail pair in
   `{(5,5),(6,2),(8,2),(9,1)}`
2. the first three branches are already symbolically closed:
   - `(5,5) -> P`
   - `(6,2) -> C`
   - `(8,2) -> O`
3. this note closes the last branch:
   - `(9,1) -> E`.

So:

> every nontrivial base-10 fixed point enters the `P/C/E/O` reduction grammar
> symbolically, not just computationally.

That completes the fixed-point all-`d` promotion step.

---

## Computational alignment

The full-corpus sweep through `d<=1000` already found:

- bad lead/tail pairs: `0`
- `(9,1)` shell-inequality failures: `0`
- non-`E` `(9,1)` rows: `0`.

So the symbolic closure above is aligned with all currently available
computation.
