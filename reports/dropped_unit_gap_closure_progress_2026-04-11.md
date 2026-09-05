# Dropped-Unit Gap Closure Progress

Date: 2026-04-11
Status: active repair note

## 1. What was repaired exactly

The key manuscript defect was not just that the old Sole Cover lemma was too optimistic. It was that the proof path switched, without warning, from:

- actual retained speeds `e = nq_e + rho_e`,

to:

- residue representatives `rho_e in {1,...,n-1}`,

in places where the floor state depends on the full speed.

This note records the first exact repair data.

### 1.1 Exact base-fibre formulas

At the canonical divisible fibre

`b_0 = L/n`,

every actual retained speed `e = nq_e + rho_e` satisfies

`floor(e b_0 / L) = q_e`.

Hence:

- if `gcd(rho_e,n)=1`, then
  `bad(e,q_e,n) = { -q_e rho_e^{-1}, -(q_e+1) rho_e^{-1} } mod n`;
- if `gcd(rho_e,n)>1`, then
  `bad(e,q_e,n) = Sol(rho_e,-q_e,n) union Sol(rho_e,-q_e-1,n)`,
  so the blocked set is controlled by cosets and divisibility, not just by the residue class.

So the base-fibre blocked set depends on the pair `(q_e, rho_e)`, not on `rho_e` alone.

### 1.2 Exact actual floor-reset criteria

Let `f = nq_f + u` be an actual retained unit speed and let `b_m = mL/f` be its `m`-th reset fibre. The departing residue is

`r_dep = -(m-1)u^{-1} mod n`.

For another actual retained speed `e = nq_e + s`, define

`sigma_f(e,m) := em mod f`.

Then `e` covers `r_dep` at `b_m` iff one of the following congruences holds:

- `sigma_f(e,m) ≡ s (mod n)`,
- `sigma_f(e,m) ≡ s + u (mod n)`.

This is the exact actual-speed replacement for the old representative-form CG1/CG2 rule.

## 2. What this immediately tells us

### 2.1 Missing unit support does not force a miss at `b_0`

A clean counterexample is:

- `n=5`,
- `E = (1,2,5,8)`,
- retained non-divisible speeds: `1,2,8`,
- residue support misses `4`.

At `b_0 = L/n = 8`, the actual blocked sets are:

- `e=1`: `{0,4}`,
- `e=2`: `{0,2}`,
- `e=8 = 5+3`: `{1,3}`.

Their union is all of `Z/5Z`. So the old inference

`missing unit residue class -> immediate miss on the initial window`

is false in this actual-speed form.

### 2.2 The repair will not be purely static at `b_0`

The same tuple `E=(1,2,5,8)` *does* have a safe fibre, but it occurs at `b=10`, the second reset of the actual unit speed `8`, not at `b_0`.

Likewise:

- `n=7`,
- `E=(1,2,3,4,7,12)`,

has a safe fibre at `b=14`, again a reset fibre of the actual unit speed `12`.

So the new formulas do not destroy the broader mechanism. They show that the honest witness geometry is more dynamic than the old Sole Cover write-up suggested.

## 3. Exploratory computational picture

I ran a small exploratory scan over tuples with:

- at least one divisible speed,
- at least one missing unit residue class,
- speeds bounded by `3n`.

Question tested:

> does there exist a safe fibre that is also a floor-reset fibre of some actual retained unit speed?

Observed counts:

- `n=4`: `76 / 88`,
- `n=5`: `845 / 846`,
- `n=6`: `2703 / 3630`.

Interpretation:

- a dynamic reset witness is very common,
- but not universal,
- so a reset-only repair is not enough by itself.

This strongly suggests a two-track repair, not a one-track replacement.

## 4. Best current repair picture

The dropped-unit gap now looks like:

### Track A: actual base-fibre exclusion geometry

Use the exact exclusion residues

- `a_low(e) = -q_e rho_e^{-1}`,
- `a_high(e) = -(q_e+1) rho_e^{-1}`,

and the non-unit coset formulas at `b_0 = L/n`.

This is the right language for any repaired static/chamber lemma.

### Track B: actual reset geometry

Use the exact congruence criteria

- `sigma_f(e,m) ≡ s`,
- `sigma_f(e,m) ≡ s+u`,

for handoff at an actual unit reset. This is the right language for any dynamic replacement of the old Sole Cover step.

## 5. Practical consequence for the manuscript

The old statement

`d notin R_non => r_d uncovered on [L/n, L/(n-1))`

should not be repaired by a cosmetic proof edit.

The correct next target is one of:

1. a genuine static chamber lemma stated in the actual coordinates `(q_e, rho_e)`, or
2. a hybrid theorem:
   base-fibre exclusion geometry + first-maintained-reset witness.

My current view is that the second route is more promising for the prime branch, while the composite dropped-unit branch may still want a separate late-window/static supplement.
