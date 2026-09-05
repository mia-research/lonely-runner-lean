# Four Lead/Tail Pair Theorem
## Positive nucleus + plateau preservation closes the first half of the global promotion step — 2026-04-24

---

## Purpose

The global promotion endgame had been stated as two remaining symbolic claims:

1. every base-10 fixed point has lead/tail pair in
   `{(5,5),(6,2),(8,2),(9,1)}`
2. every `(9,1)` fixed point satisfies the shell inequalities needed to force
   the `E` family.

This note closes the first item cleanly.

The key point is that the lead/tail pair is already determined at the level of
the positive nucleus, and terminal zero plateaus do not change it.

So no new lead/tail branch can appear beyond the positive no-zero theorem.

---

## Setup

Let

`g = (g_1, ..., g_h)`

be the nonincreasing gap profile of a nontrivial base-10 fixed point, with:

- `r` = trailing-zero count,
- `m = h-r`,
- positive nucleus

  `u = (g_1, ..., g_m)`.

Write:

- `alpha = g_1`
- `beta = g_m`

for the lead/tail pair of the full fixed point.

Because the plateau is terminal, the positive part of the gap profile is
exactly the nucleus `u`. Therefore the lead/tail pair of the full profile is
the same as the lead/tail pair of the nucleus.

So:

> lead/tail classification for arbitrary fixed points reduces immediately to
> lead/tail classification for positive no-zero nuclei.

---

## Positive no-zero nuclei

By the positive no-zero gap theorem, every positive no-zero nucleus lies in
exactly one of the five families:

1. `(5)`
2. `(6,3^m,2)`
3. `(8,6,4,3^m,2)`
4. `(9^a,7^k,5^k,3^d,1^k)`
5. `(9^a,8,7^k,6,5^k,4,3^d,2,1^k)`.

Their lead/tail pairs are immediate:

1. `(5)` gives `(5,5)`
2. `(6,3^m,2)` gives `(6,2)`
3. `(8,6,4,3^m,2)` gives `(8,2)`
4. `(9^a,7^k,5^k,3^d,1^k)` gives `(9,1)`
5. `(9^a,8,7^k,6,5^k,4,3^d,2,1^k)` gives `(9,1)`.

So every positive no-zero nucleus already has lead/tail pair in

`{(5,5),(6,2),(8,2),(9,1)}`.

---

## Plateau preservation

By the borrow normal form with plateau:

- the terminal zero plateau contributes only a central block of `9`s,
- it does not create any new positive outer shell value,
- it does not change the last positive gap value.

Equivalently:

> if a fixed point has nucleus `u`, then the full profile and the nucleus have
> exactly the same lead/tail pair.

So no plateau lift can create a fifth lead/tail branch.

---

## Theorem

Let `n` be a nontrivial base-10 Kaprekar fixed point with gap profile `g`.

Then its lead/tail pair `(alpha,beta)` belongs to

`{(5,5),(6,2),(8,2),(9,1)}`.

### Proof

Take the positive nucleus `u` of `g`.

By the positive no-zero theorem, `u` belongs to one of the five classified
families above, hence has lead/tail pair in

`{(5,5),(6,2),(8,2),(9,1)}`.

By plateau preservation, `g` has the same lead/tail pair as `u`.

Therefore `g` also has lead/tail pair in

`{(5,5),(6,2),(8,2),(9,1)}`.

This proves the theorem.

---

## Consequence for the global promotion step

The first half of the endgame is now symbolic.

The only remaining genuine entrance problem is:

> prove that every `(9,1)` fixed point satisfies the shell inequalities
> `A>=q`, `B>=q`, `C>=q`, `D>q`.

Once those inequalities are established, the `(9,1)` branch is exactly `E` by
the existing shell-reduction note.

So the all-`d` promotion step has now narrowed to one branch and one resource
lemma chain.

---

## Relation to the computational sweep

The full-corpus sweep through `d<=1000` already found no bad lead/tail pairs.
This note explains why that should be expected structurally:

- the pair is fixed at the nucleus level,
- plateau lifting cannot change it.

So the sweep is no longer carrying any conceptual burden on the lead/tail side.
