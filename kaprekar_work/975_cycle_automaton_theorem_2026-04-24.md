# 975 Cycle Automaton Theorem
## The higher-dimensional `975` cycle side is an exact borrow-state automaton — 2026-04-24

---

## Purpose

The fixed-point side is now closed, so the next natural target is the cycle
side.

The most visible higher-dimensional cycle phenomenon already in the project is
the `975` period-3 family at:

- `d=12`
- `d=16`
- `d=22`

This note shows those are not isolated examples.

They sit inside one exact symbolic cycle automaton, and the familiar `975`
fixed points are the degenerate ridge of the same family.

So the cycle story begins much more cleanly than “three special examples”.

---

## Statement

For integers

- `a,b,c >= 1`
- `m >= 0`

define three phase states by their digit-frequency vectors:

### Phase 0

`X0(a,b,c,m) = [1, a, c, m, b, b, m, c, a, 1]`

### Phase 1

`X1(a,b,c,m) = [1, b, a, m, c, c, m, a, b, 1]`

### Phase 2

`X2(a,b,c,m) = [1, c, b, m, a, a, m, b, c, 1]`

Then:

`K(X0) = X1`

`K(X1) = X2`

`K(X2) = X0`.

Therefore:

- if `a=b=c`, the orbit collapses to a fixed point
- if `(a,b,c)` is not constant, the orbit has exact period `3`

and has dimension

`d = 2 + 2(a+b+c+m)`.

---

## Gap-profile formulas

The three phases have exact shell-gap profiles:

### Phase 0

`g0 = (9, 7^a, 5^c, 3^m, 1^b)`

### Phase 1

`g1 = (9, 7^b, 5^a, 3^m, 1^c)`

### Phase 2

`g2 = (9, 7^c, 5^b, 3^m, 1^a)`.

This is already the main mechanism:

> the Kaprekar map acts by cyclically permuting the exponents on
> `7 / 5 / 1`, while leaving the `3`-block fixed.

So the `975` cycle family is an exact borrow-state automaton on the exponent
triple `(a,b,c)` with frozen shell parameter `m`.

---

## Proof

Take Phase 0:

`X0(a,b,c,m) = [1, a, c, m, b, b, m, c, a, 1]`.

Its sorted digits are:

`9^1 8^a 7^c 6^m 5^b 4^b 3^m 2^c 1^a 0^1`.

Shell pairing from the outside is exact:

1. `9-0` once, giving `9`
2. `8-1` exactly `a` times, giving `7^a`
3. `7-2` exactly `c` times, giving `5^c`
4. `6-3` exactly `m` times, giving `3^m`
5. `5-4` exactly `b` times, giving `1^b`

So

`g0 = (9, 7^a, 5^c, 3^m, 1^b)`.

Now use the tail-`1` borrow reconstruction formulas.
For any profile of the form

`g = (9, 7^u, 5^v, 3^w, 1^t)`

the digit counts are:

- `c0 = c9 = 1`
- `c1 = c8 = t`
- `c2 = c7 = u`
- `c3 = c6 = w`
- `c4 = c5 = v`.

Applying that to `g0` gives:

`K(X0) = [1, b, a, m, c, c, m, a, b, 1] = X1(a,b,c,m)`.

The Phase 1 and Phase 2 cases are identical by cyclic symmetry:

- `g1 = (9, 7^b, 5^a, 3^m, 1^c)` gives `K(X1)=X2`
- `g2 = (9, 7^c, 5^b, 3^m, 1^a)` gives `K(X2)=X0`

which proves the theorem.

---

## Fixed ridge versus period-3 region

If `a=b=c=k`, then the three phases coincide:

`X0(k,k,k,m) = X1(k,k,k,m) = X2(k,k,k,m)`.

So the automaton collapses to a fixed point.

Examples:

- `(1,1,1,0)` gives `97508421`
- `(1,1,1,1)` gives `9753086421`

If `(a,b,c)` is not constant, the cyclic shift

`(a,b,c) -> (b,c,a) -> (c,a,b) -> (a,b,c)`

cannot collapse in one step, and because a 3-cycle has no 2-cycle subcase, the
orbit has exact period `3`.

So the family splits cleanly into:

- a fixed ridge `a=b=c`
- a period-3 region `a,b,c` not all equal.

---

## Known project examples as slices of the theorem

The previously isolated `975` cycle members are now just parameter slices:

### `d=12`

`(a,b,c,m) = (1,1,2,1)`

gives the cycle:

- `977530864221`
- `975530864421`
- `975310886421`

### `d=16`

`(a,b,c,m) = (1,2,3,1)`

gives the cycle:

- `9777553086442221`
- `9755531088644421`
- `9775311088864221`

### `d=22`

`(a,b,c,m) = (2,3,3,2)`

gives the cycle:

- `9777555331088664442221`
- `9775553311088866444221`
- `9777553311088866442221`

So the old `d=12,16,22` record is not “three cycle sightings”.
It is three visible points on one exact parametric cycle automaton.

---

## Shell-extension reading

This family also carries a clean shell-extension interpretation.

The parameter `m` is the frozen `3`-block, so:

- `m -> m+1`

adds the complementary pair `(3,6)` uniformly to all three phases.

The parameters `a,b,c` are phase-rotating shell weights:

- increasing `a` by `1` adds:
  - `(1,8)` to Phase 0
  - `(2,7)` to Phase 1
  - `(4,5)` to Phase 2

- increasing `b` by `1` adds:
  - `(4,5)` to Phase 0
  - `(1,8)` to Phase 1
  - `(2,7)` to Phase 2

- increasing `c` by `1` adds:
  - `(2,7)` to Phase 0
  - `(4,5)` to Phase 1
  - `(1,8)` to Phase 2

So the family is not only an automaton.
It is also closed under explicit shell-extension moves.

That is exactly the type of structure we were hoping to find on the cycle side.

---

## Computational validation

Runner:

- `scripts/kaprekar_975_cycle_automaton.py`

Machine output:

- `analysis/base10/kaprekar_975_cycle_automaton_2026-04-24.json`

Validation grid:

- `a,b,c in {1,...,8}`
- `m in {0,...,8}`

Results:

- parameter points checked: `4608`
- failures: `0`
- fixed-ridge points: `72`
- period-3 points: `4536`

So the symbolic automaton law is aligned with a broad parameter sweep, not just
the historically known `d=12,16,22` slices.

---

## Consequence for the cycle program

This is the cycle-side analogue of the fixed-point grammar breakthrough.

We now have:

- a 2-digit exact gap-cycle mechanism
- a `d=5` exact dead-zone automaton
- a `d=7` exact dead-zone automaton
- and now an exact higher-dimensional period-3 automaton on the `975` side

So the cycle program is no longer starting from scattered curiosities.
It now starts from exact symbolic automata plus shell-extension rules.

That is the right language for the next step.
