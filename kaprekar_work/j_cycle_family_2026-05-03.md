# The `J` Residual Period-3 Family on the Odd Rotor Side

## Purpose

The `H` shell-fan note explained the odd period-3 census at:

- `d=21` exactly,
- `d=23` exactly,

but at `d=25` there was one residual period-3 family left over after the
four-direction shell fan closure.

This note identifies that residual exactly.

## Residual representative

The missing period-3 cycle at `d=25` has representative

`J_0^(0) = (1,3,3,1,4,4,1,3,3,2)`.

Comparing with

`H_0^(0) = (1,2,2,1,3,3,1,2,2,2)`

shows the residual difference is

`E = (0,1,1,0,1,1,0,1,1,0)`

which is exactly:

- one `(1,8)` shell,
- one `(2,7)` shell,
- one `(4,5)` shell,

added **uniformly across all three phases**.

So the residual is

`J_m = H_m + E`

with

`E = +18 +27 +45`.

## Exact family law

For every `m >= 0`, define

- `J_0(m) = H_0(m) + E`
- `J_1(m) = H_1(m) + E`
- `J_2(m) = H_2(m) + E`

Then exactly:

- `K(J_0(m)) = J_1(m)`
- `K(J_1(m)) = J_2(m)`
- `K(J_2(m)) = J_0(m)`

So `J_m` is an exact period-3 family for all `m`.

The verification checked `m = 0..20` with:

- failures: `0`

## Meaning for the `H` shell fan

This changes the interpretation of the `d=25` residual.

It is **not** an unexplained odd period-3 exception.
It is an exact new family on the same rotor side:

- base channel: `H_m = H + A`
- shell fan through degree `2`: exact
- first residual at degree `3`: the exact `J_m` family

So the odd period-3 side now has:

1. the axial chain `H_m`,
2. a four-direction shell fan through `d=23`,
3. one exact residual family `J_m` already visible at `d=25`.

That is still not a complete rotor theorem, but it is much better than
“one unexplained residual.”

## Structural reading

The shell

`E = +18 +27 +45`

is the uniform odd complement of the old axial shell

`A = +36`.

So the `J` family is the first place where the rotor side shows a genuinely
new **uniform odd triple-shell direction**, rather than only the mixed
phase-rotating directions of the original `H` shell fan.

That is the right way to read the `d=25` residual.
