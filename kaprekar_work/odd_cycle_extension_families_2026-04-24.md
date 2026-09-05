# Odd Cycle Extension Families

## Claim

The odd-side cycle phenomena at `d=11` and `d=13` are not isolated accidents.
They organize into four exact automaton families, all propagated by the same
uniform shell move

`+2_{36}`.

That is, increasing the parameter `m` by `1` always means:

- add one `3`,
- add one `6`,
- to every phase state.

## Family `A_m` — period 5

Dimensions:

`d = 11 + 2m`, `m >= 0`

Phase states:

- `A0(m) = [0,2,0,m+2,1,1,m+2,1,0,2]`
- `A1(m) = [0,2,1,m+1,1,1,m+1,1,2,1]`
- `A2(m) = [0,1,2,m+1,1,1,m+1,2,1,1]`
- `A3(m) = [0,1,1,m+1,2,2,m+1,1,1,1]`
- `A4(m) = [1,0,2,m+1,1,1,m+1,1,2,1]`

Exact dynamics:

- `K(A0)=A1`
- `K(A1)=A2`
- `K(A2)=A3`
- `K(A3)=A4`
- `K(A4)=A0`

So `A_m` has exact period `5` for every `m`.

Base slice:

- `m=0`, `d=11` is the known period-5 odd cycle.

First lift:

- `m=1`, `d=13` is one of the three known period-5 cycles.

## Family `B_m` — period 2

Dimensions:

`d = 13 + 2m`, `m >= 0`

Phase states:

- `B0(m) = [0,1,1,m+2,2,2,m+3,0,0,2]`
- `B1(m) = [1,0,3,m+2,0,0,m+2,2,2,1]`

Exact dynamics:

- `K(B0)=B1`
- `K(B1)=B0`

So `B_m` has exact period `2` for every `m`.

Base slice:

- `m=0`, `d=13` is the known odd period-2 cycle.

## Family `C_m` — period 5

Dimensions:

`d = 13 + 2m`, `m >= 0`

Phase states:

- `C0(m) = [0,1,2,m+1,2,2,m+1,2,1,1]`
- `C1(m) = [1,0,2,m+1,2,2,m+1,1,2,1]`
- `C2(m) = [1,1,1,m+2,1,1,m+2,1,1,2]`
- `C3(m) = [0,3,0,m+2,1,1,m+2,1,1,2]`
- `C4(m) = [0,2,2,m+1,1,1,m+1,2,2,1]`

Exact dynamics:

- `K(C0)=C1`
- `K(C1)=C2`
- `K(C2)=C3`
- `K(C3)=C4`
- `K(C4)=C0`

So `C_m` has exact period `5` for every `m`.

Base slice:

- `m=0`, `d=13` is a second odd period-5 cycle.

## Family `D_m` — period 5

Dimensions:

`d = 13 + 2m`, `m >= 0`

Phase states:

- `D0(m) = [0,2,1,m+1,2,2,m+1,1,2,1]`
- `D1(m) = [1,0,3,m+1,1,1,m+1,2,2,1]`
- `D2(m) = [0,2,0,m+2,2,2,m+2,1,0,2]`
- `D3(m) = [1,1,2,m+1,1,1,m+1,1,3,1]`
- `D4(m) = [0,2,1,m+2,1,1,m+2,2,0,2]`

Exact dynamics:

- `K(D0)=D1`
- `K(D1)=D2`
- `K(D2)=D3`
- `K(D3)=D4`
- `K(D4)=D0`

So `D_m` has exact period `5` for every `m`.

Base slice:

- `m=0`, `d=13` is the third odd period-5 cycle.

## Shared shell direction

All four families are preserved by the same lift:

- `m -> m+1`
- add one `3`
- add one `6`
- to every phase state.

So the odd-side cycle extension story is noticeably more rigid than it first
looked: the different odd cycle families share one shell direction.

## The unstable lifted period-8 orbit

There is also the genuine period-8 cycle at `d=11`. Its lifted version is not
closed.

Let `T_m` be the family obtained by adding the same `+2_{36}` lift to the
eight phase states of the `d=11` period-8 orbit.

Then for every `m >= 1`, `T_m` is **not** an 8-cycle. Instead it enters the
period-2 family `B_{m-1}` in bounded time.

The phase-dependent hit times are constant across all tested `m`:

- hits after steps `[4,3,2,1,1,1,6,5]`

So the old `d=11` period-8 orbit behaves like a low-dimensional unstable seed:

- exact cycle at `m=0`,
- but under the shared odd shell lift it collapses into the stable period-2
  branch.

## Computational validation

The runner

- `scripts/kaprekar_odd_cycle_extension_families.py`

checked:

- `A_m` for `m = 0..20`
- `B_m` for `m = 0..20`
- `C_m` for `m = 0..20`
- `D_m` for `m = 0..20`
- the transient reduction `T_m -> B_{m-1}` for `m = 1..20`

Results:

- `A`: `21` checked, `0` failures
- `B`: `21` checked, `0` failures
- `C`: `21` checked, `0` failures
- `D`: `21` checked, `0` failures
- `T -> B`: `160` checked phase points, `0` failures

## Interpretation

This is a real step toward a cycle grammar.

The odd-side story is no longer:

- one period-5 cycle at `d=11`,
- one period-2 cycle at `d=13`,
- two more period-5 cycles at `d=13`,
- plus an awkward period-8 orbit.

It is now:

- four exact odd automaton families sharing one shell-extension direction,
- plus one unstable low-dimensional seed that reduces into one of those
  families after lifting.
