# Cycle Kernel Birth Inventory

## Purpose

The cycle grammar skeleton says:

- there is a shared shell axis `L36`,
- stable families are exact under that lift,
- some low-dimensional kernels are unstable and reduce into stable branches.

This note asks the next sharper question:

> where do genuinely new primitive cycle kernels first appear?

Here “primitive” means primitive under the shared shell axis `L36`: a stable
cycle family is born at its `m=0` slice.

## Shared shell axis

The common higher-dimensional lift is

`L36 : add one digit 3 and one digit 6 to every phase state`.

So each stable family has a primitive kernel at its smallest dimension.

## Even-side births

### `863` chain

Primitive birth:

- `d=8`

This is the unique period-7 count-space kernel on the even side.

Its descendants are:

- `d = 8 + 2m`

under repeated `L36`.

### `975` period-3 kernels

The `975` family is multi-parameter:

- `X0(a,b,c,m) = [1,a,c,m,b,b,m,c,a,1]`
- `X1(a,b,c,m) = [1,b,a,m,c,c,m,a,b,1]`
- `X2(a,b,c,m) = [1,c,b,m,a,a,m,b,c,1]`

with

- `a,b,c >= 1`
- `m >= 0`

and `K` cyclically permuting `(a,b,c)`.

Primitive under `L36` means `m=0`, so the birth dimension is

`d = 2(1+a+b+c)`.

Therefore:

- new `975` primitive kernels are born at **every even dimension `d >= 10`**
  for which there exists a positive nonconstant triple
  `a+b+c = d/2 - 1`.

So the even side already follows a clear birth rule:

- one exceptional period-7 kernel at `d=8`,
- then an infinite period-3 kernel stream at every even `d >= 10`.

## Odd-side births observed exactly

Exact count-space scans now reach:

- `d=11`
- `d=13`
- `d=15`
- `d=17`
- `d=19`

The stable primitive kernels under `L36` are:

- `d=11`: `A_0` (period `5`)
- `d=13`: `B_0` (period `2`), `C_0` (period `5`), `D_0` (period `5`)
- `d=15`: `E_0` (period `5`), `F_0` (period `5`)
- `d=17`: `G_0` (period `5`)
- `d=19`: `H_0` (period `3`)

So the odd-side primitive birth counts through `d=19` are:

- `11 -> 1`
- `13 -> 3`
- `15 -> 2`
- `17 -> 1`
- `19 -> 1`

This is already enough to rule out the simplest wrong model:

> the odd side is **not** just one or two kernels lifting forever.

New kernels continue to appear at later odd dimensions.

## Unstable births

There is also an unstable primitive kernel at:

- `d=11`: the period-8 orbit `T_0`

It is exact at `d=11`, but after one or more `L36` lifts it does not remain a
closed period-8 family. Instead it reduces into the stable period-2 family
`B`.

So the birth inventory needs two categories:

- stable primitive kernels,
- unstable primitive kernels.

## Current birth picture

### Stable births

- even:
  - `Y_0` at `d=8`
  - `975` primitive kernels at every even `d >= 10`
- odd:
  - `A_0` at `d=11`
  - `B_0,C_0,D_0` at `d=13`
  - `E_0,F_0` at `d=15`
  - `G_0` at `d=17`
  - `H_0` at `d=19`

### Unstable births

- `T_0` at `d=11`

## What rule is visible already?

A partial rule is now visible:

1. **Parity controls the birth channel.**
   - even births are dominated by the `975` stream plus the single `863`
     kernel;
   - odd births appear as a separate family inventory.

2. **The shell operator is shared even when kernels differ.**
   - all currently known higher-dimensional stable families, even and odd,
     propagate by the same `L36` axis.

3. **Odd births continue beyond `d=13`.**
   - the odd primitive inventory is still growing at `d=15,17,19`.

So the honest current answer is:

> birth dimensions do not look ad hoc, but we do not yet have a closed formula
> for odd kernel multiplicity.

What we do have is a strong structural conjecture:

> primitive cycle kernels are born on parity-respecting dimensions, then evolve
> under a universal `L36` shell axis, with unstable kernels reducing into
> stable families.

## Immediate next target

The next clean step is now:

> characterize the odd primitive kernels themselves.

That means finding whether `A,B,C,D,E,F,G,H,...` are instances of one or two
deeper odd kernel templates, rather than a growing alphabet of unrelated seeds.
