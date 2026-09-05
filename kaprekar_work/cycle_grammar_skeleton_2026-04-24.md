# Cycle Grammar Skeleton

## Purpose

The fixed-point side is already expressed as:

- primitive kernels,
- shell moves,
- reduction grammar.

This note records the first comparable skeleton on the cycle side.

It is not yet a complete `d=all` cycle theorem. But it is a genuine grammar
shape:

- a small inventory of primitive cycle kernels,
- one shared shell axis,
- one richer transverse shell system on the `975` side,
- and unstable kernels that reduce into stable families after lift.

## Universal shell axis

Across all currently known higher-dimensional count-space cycle families except
the low-dimensional 2-digit core and the dead-zone automata, one shell move
keeps reappearing:

`L36 : add one digit 3 and one digit 6 to every phase state`

This raises dimension by `2`.

Families already known to be exactly closed under `L36`:

- `863` period-7 family
- odd `A` period-5 family
- odd `B` period-2 family
- odd `C` period-5 family
- odd `D` period-5 family
- odd `E` period-5 family
- odd `F` period-5 family
- the `m`-axis of the `975` family

So `L36` is the first genuine universal cycle-shell operator in base 10.

## Stable kernels currently on the table

### 1. Low-dimensional exact cycle kernel

- 2-digit gap cycle
- exact gap map `T(g)=|2g-11|`
- one unique nonzero cycle

This is the smallest cycle kernel.

### 2. Dead-zone borrow automata

- `d=5`: three attractors, periods `2,4,4`
- `d=7`: one universal 8-cycle

These are finite automata with no nontrivial shell family yet known.

### 3. `975` kernel family

The `975` side is special because it has:

- the universal `L36` axis,
- plus transverse rotating complementary-pair shell moves.

Its exact phase states are parameterized by

- `(a,b,c,m)`, with `a,b,c >= 1`, `m >= 0`

and `K` cyclically permutes `(a,b,c)`.

So this is already a true multi-parameter cycle grammar, not just one chain.

### 4. `863` kernel family

The unique period-7 count-space cycle at `d=8` extends under `L36` to all
even dimensions

`d = 8 + 2m`.

This gives one exact period-7 chain.

### 5. Odd stable kernel families

The odd side now has eight exact stable families:

- `A_m` — period `5`, `d = 11 + 2m`
- `B_m` — period `2`, `d = 13 + 2m`
- `C_m` — period `5`, `d = 13 + 2m`
- `D_m` — period `5`, `d = 13 + 2m`
- `E_m` — period `5`, `d = 15 + 2m`
- `F_m` — period `5`, `d = 15 + 2m`
- `G_m` — period `5`, `d = 17 + 2m`
- `H_m` — period `3`, `d = 19 + 2m`

All are exactly closed under `L36`.

So by `d=19` the odd-side cycle story is already branching: one shell axis,
multiple primitive kernels.

But the raw labels `A,B,C,D,E,F,G,H` are not the final structure. The current
odd-kernel template probe suggests a deeper compression:

- one period-5 staircase channel containing `A,C,D,E,F,G` as observed slices,
- one period-3 rotor channel beginning at `H`,
- one low-dimensional boundary degeneration at `B`.

So the odd side looks less like “many unrelated kernels” and more like “two
template channels plus one boundary seed.”

The period-5 side is now sharper than that first compression note suggested.
It already has:

- one canonical phase gauge,
- one fixed 5-piece layer operator,
- one closed-form cumulative staircase,
- and a ridge-collapse rule at level `5`.

So the observed kernels `A,C,F,G` are consecutive staircase levels, while
`D,E` are a decorated slice of the same operator rather than a second growth
mechanism.

And the new bridge result says what sits next to that ridge:

- the staircase closes onto the fixed count ridge
  `R = (1,2,2,2,2,2,2,2,2,2)`,
- the period-3 family `H` is exactly the minimal rotating defect of that ridge,
  obtained by removing one `(3,6)` shell and reinserting it into one of
  `(4,5)`, `(1,8)`, `(2,7)`.

So the period-5 and period-3 odd channels are now connected by one explicit
ridge/defect mechanism rather than by vague proximity.

That connection is now tighter than the bridge note itself originally claimed.
Two further closure steps are now in place:

- the raw count-space staircase pieces `N_0,...,N_4` are forced uniquely by
  the gap-space pieces `M_0,...,M_4` together with the odd asymmetry alphabet
  `{u,v,w}`,
- among all `20` minimal one-shell transfers away from the ridge, exactly
  three are primitive `H` rotor directions:
  - `36 -> 18`
  - `36 -> 27`
  - `36 -> 45`

The three transfers

- `18 -> 09`
- `27 -> 09`
- `45 -> 09`

also enter `H`, but only after a transient, so they are captures rather than
primitive defect directions.

So the odd-side bridge picture is now:

- staircase operator forced in both gap space and count space,
- staircase closes onto a fixed ridge,
- the ridge has exactly three primitive one-shell rotor exits,
- and those exits are precisely the `H` family.

That rotor side is now sharper too. The reduced odd-state census at

- `d=21`
- `d=23`
- `d=25`

shows that `H` is not just one old axial chain `H_m`. It already carries a
small transverse shell fan.

On top of the base rotor `H`, define four degree-1 shell directions:

- `A = +36` uniformly
- `B = +09` uniformly
- `C = +(45,18,27)` across the three phases
- `D = +(27,45,18)` across the three phases

Then:

- at `d=21`, the period-3 sector is **exactly** the degree-1 shell fan
  `{A,B,C,D}`
- at `d=23`, the period-3 sector is **exactly** the commutative degree-2
  closure of those four directions
- at `d=25`, the same shell-fan construction still explains `20` of the `21`
  period-3 attractors, leaving one honest residual

So the odd period-3 side is already far more structured than a single
`H_m` chain. It is a genuine shell fan.

And the former `d=25` residual is now also explained exactly:

- `J_m = H_m + (18 + 27 + 45)` uniformly across phases

is an exact period-3 family for every `m >= 0`.

So the old “one residual at degree 3” is not a stray exception after all. It
is the first genuinely new uniform odd triple-shell direction on the rotor
side.

The odd period-3 side therefore currently reads as:

- one axial chain `H_m`,
- one transverse shell fan through degree `2`,
- one exact residual family `J_m` already visible at degree `3`.

That description is now sharper. `J` is not best treated as a sixth ordinary
degree-1 shell direction. It is the first exposed **weight-3** direction on
top of `H`:

- `A = +36` uniformly, weight `1`
- `B = +09` uniformly, weight `1`
- `C = +(45,18,27)` by phase, weight `1`
- `D = +(27,45,18)` by phase, weight `1`
- `E = +(18+27+45)` uniformly, weight `3`

If `W_r` denotes the weighted closure of `H` under these directions with total
weight `r`, then `W_r` lives at

`d = 19 + 2r`

and the exact low-weight counts are

- `|W_1| = 4` at `d=21`
- `|W_2| = 10` at `d=23`
- `|W_3| = 21` at `d=25`

matching the reduced-state period-3 census exactly.

The closure-size formula is then

`N_3(r) = sum_{e=0}^{floor(r/3)} C(r-3e+3, 3)`.

And the higher odd samples now line up with that weighted closure cleanly:

- `d=27`, `r=4`: sampled period-3 count `39`, misses `0`
- `d=29`, `r=5`: sampled period-3 count `66`, misses `0`
- `d=31`, `r=6`: sampled period-3 count `105`, misses `0`
- `d=33`, `r=7`: sampled period-3 count `159`, misses `0`

So the reduced odd period-3 side is now best read as a **weighted rotor fan**,
not as an ever-growing alphabet of unrelated residual families.

This weighted fan has an exact affine normal form. Every currently exact odd
period-3 cycle representative in the reduced high-minus-low=`1` sector at

- `d=25`
- `d=27`
- `d=29`

fits the phase law

- `R0(u,v,w,x,y) = [u,v,w,x,y,y,x,w,v,u+1]`
- `R1(u,v,w,x,y) = [u,y,v,x,w,w,x,v,y,u+1]`
- `R2(u,v,w,x,y) = [u,w,y,x,v,v,x,y,w,u+1]`

with

- `u >= 1`
- `x >= 1`
- `v >= 2`
- `w >= v`
- `y >= v+1`

and the generator coordinates are exactly

- `B = u-1`
- `E = v-2`
- `D = w-v`
- `A = x-1`
- `C = y-v-1`

So the five shell directions are now identified as the natural Hilbert-basis
increments of the affine rotor cone, not just as an empirical generator list.

At the same time, the odd period-2 side currently looks much smaller. In the
same `d=27,29,31,33` samples, the only observed period-2 attractor is the old
`B` line. So the extra period-2 attractor seen at `d=25` currently reads as a
low-dimensional boundary knot rather than as evidence for a second continuing
period-2 chain.

That knot is now sharper too. In its natural symmetric boundary ansatz

`Q(w,x,y) = [0,2,w,x,y,y,x,w,2,3]`

there is exactly one nontrivial period-2 cycle:

- `Q(3,3,3) <-> Q(4,2,3)`

and it is terminal under one-shell lifts: no ordered pair of one-shell
additions to its two phases yields a new period-2 cycle at `d=27`.

So the reduced odd period-2 picture currently is:

- one continuing boundary line `B`
- one isolated low-dimensional boundary knot at `d=25`

That local picture is now known to be only part of the global odd story.
The apparent `d=25` knot is not a singleton accident. It belongs to the
explicit boundary thread

`K_p = [0,p,3,3,3,3,3,3,p,3]`

of dimension `d=21+2p`.

This thread now has an exact verified phase diagram:

- `p=1,2`: period `2`
- `p=3`: fixed
- `p=4..7`: period `5` after finite preperiod
- `p=8`: fixed
- `p>=9`: enters the exact period-3 family
  - `Z0(r) = [1,r,4,4,4,4,4,4,r,4]`
  - `Z1(r) = [1,4,r,4,4,4,4,r,4,4]`
  - `Z2(r) = [1,4,4,4,r,r,4,4,4,4]`
  with `r=p-4`

So the old `d=23` and `d=25` period-2 knots are just the first nontrivial
phases of a broader odd boundary thread.

This also corrects the global scope of the affine rotor note:

- the affine rotor cone still appears exact for the reduced high-minus-low=`1`
  odd period-3 sector,
- but it is not yet the whole odd period-3 story globally, because the
  boundary thread `K_p` eventually produces a second explicit period-3 family
  on a different high-minus-low level.

That split is now cleaner algebraically than this note originally recorded.
The reduced rotor cone and the boundary-thread tail are both levels of one odd
affine-delta normal form

- `R0_delta(u,v,w,x,y) = [u,v,w,x,y,y,x,w,v,u+delta]`
- `R1_delta(u,v,w,x,y) = [u,y,v,x,w,w,x,v,y,u+delta]`
- `R2_delta(u,v,w,x,y) = [u,w,y,x,v,v,x,y,w,u+delta]`

with `delta = c9-c0`.

What is currently exact:

- reduced odd period-3 census at `d=23,25,27,29` lies on level `delta=1`
- the boundary-thread tail `Z_r` is the explicit slice
  `Ri_delta(1,r,4,4,4)` on level `delta=3`
- the exact lift
  `R_delta(u,v,w,x,y) -> R_{delta+2}(u,v+2,w+2,x+2,y+2)`
  propagates odd affine levels upward
- the exact entrance law
  `K^12(K_p)=Z0(p-4)` for `p>=8`
  feeds the non-period-3 boundary thread into level `delta=3`

So the odd period-3 side is now better read as exposed affine levels than as
“one cone plus a correction.”

And that picture is already larger than just `delta=1` and the `K_p` tail.
The direct affine-delta scan now shows:

- reduced odd period-3 is the exact level `delta=1`
- the `K_p` tail is one explicit entrance line inside level `delta=3`
- the larger affine hierarchy already continues through all positive odd
  `delta`, via the exact `delta -> delta+2` lift

So the boundary thread is not the whole higher-asymmetry story. It is the
first explicit constructive slice of the next affine level.

## Unstable kernels

There is at least one explicit unstable seed:

- the genuine period-8 cycle at `d=11`

Under the same shell lift `L36`, it does not remain closed. Instead, for every
tested lift level `m >= 1`, it falls into the stable period-2 family `B_{m-1}`
in bounded phase-dependent time.

And `B` is no longer best treated as a fully separate primitive species.
It can be absorbed as a boundary repair of `T`:

- `B_0(m) = T_0(m) + 45`
- `B_1(m) = T_5(m) + 36`

for every `m >= 0`.

So the cycle grammar is not purely “stable families under shell lift”. It also
has:

- unstable primitive kernels,
- and reduction from unstable to stable branches.

That is already much closer to the fixed-point grammar than a raw list of
observed cycle lengths.

## Current grammar picture

The current best cycle-side skeleton is:

1. choose a primitive cycle kernel,
2. evolve it under shell operators,
3. either:
   - stay inside a stable family,
   - move transversely inside a multi-parameter family (`975`),
   - or reduce into a stable family after a transient.

So the right grammar objects are:

- primitive kernels,
- shell operators,
- family closures,
- reduction rules.

## What this does and does not say

What is established:

- the cycle side is not random,
- there is a real universal shell axis `L36`,
- several exact higher-dimensional cycle families exist,
- unstable low-dimensional seeds can reduce into stable branches.

What is not established:

- a complete base-10 `d=all` cycle classification,
- a proof that `L36` is the only universal cycle shell operator,
- a complete primitive-kernel inventory.

The sharpest currently visible cycle-side gap is now:

- complete the `H` shell fan beyond the `J` family,
- understand the remaining odd period-2 boundary sector beyond the absorbed
  `B` line,
- and decide whether further odd births stay inside these rotor/boundary
  channels or force genuinely new mechanisms.

## Computational support

The inventory runner

- `scripts/kaprekar_cycle_grammar_inventory.py`

verifies through `m <= 20`:

- `863` period-7 family
- odd families `A,B,C,D,E,F,G,H`
- reduction of lifted period-8 family `T` into `B`

with zero failures.

The `975` family is verified separately in

- `analysis/base10/975_cycle_automaton_theorem_2026-04-24.md`

because it carries additional transverse shell operators beyond the shared
`L36` axis.

## Interpretation

This is the first point where the cycle program has a plausible grammar-level
shape:

- one shared shell axis,
- one known transverse shell system,
- several stable families,
- and explicit unstable-to-stable reductions.

That is enough structure to stop treating cycles as a bag of exceptions.

The next sharpening after this note is:

- compress the odd kernel alphabet into template channels,
- then ask whether new odd births continue inside those channels rather than
  spawning wholly new mechanisms.
