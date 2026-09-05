# Base-Fibre Thinness Reassessment

Date: 2026-04-12
Status: correction / pivot note

## 1. What failed

The earlier candidate

> **BF.1**: if the dropped-unit base fibre `b_0=L/n` is fully covered, then some residue has multiplicity `1` at `b_0`

is **false in general**.

It held throughout the bounded low-speed scans up to:

- `n=10` with speeds `<= 2n`,

but it fails for larger actual speeds.

## 2. Explicit counterexample

Take

- `n = 10`,
- `E = (4,23,28,49,55,74,76,105,110)`.

Then:

- `E_div = {110}`,
- `E_non = {4,23,28,49,55,74,76,105}`,
- `R_non = {3,4,5,6,8,9}`,
- the missing unit residue classes are `{1,7}`.

At the base fibre `b_0 = L/10`, the blocked sets are:

- `4  -> {0,5}`,
- `23 -> {6,9}`,
- `28 -> {1,6}`,
- `49 -> {4,5}`,
- `55 -> {1,3,5,7,9}`,
- `74 -> {3,8}`,
- `76 -> {2,7}`,
- `105 -> {0,2,4,6,8}`.

So the multiplicities are

`(m_0(0),...,m_0(9)) = (2,2,2,2,2,3,3,2,2,2)`.

Hence:

- the base fibre is fully covered,
- but **no residue has multiplicity `1`**.

This is a genuine dropped-unit configuration, so BF.1 cannot be the general repair theorem.

## 3. Why this is still informative

The counterexample does not destroy the transport picture. It sharpens it.

In the example above:

- the canonical target `r_1 = 9` is patched by `23` and `55`,
- yet the first safe fibre still appears later,
- at the reset of runner `105`,
- with residue `4` becoming uncovered.

So the safe fibre is again created by **migration of burden**, but the starting state is not multiplicity `1`. It is multiplicity `2`.

This means the true thin object is not necessarily:

> “a uniquely covered residue at `b_0`.”

It may instead be:

> “a residue whose repair network has width `2` and bounded lifetime.”

That is a better fit for the general transport programme.

## 4. Revised candidate invariant

The strongest surviving replacement currently supported by all bounded scans and random large-speed probes is:

> **BF.2 (candidate).** In the dropped-unit branch, if `b_0=L/n` is fully covered, then some residue has multiplicity at most `2` at `b_0`.

Evidence so far:

- exhaustive scans:
  - `n=5,6` with speeds `<=3n`,
  - `n=7,8,9,10` with speeds `<=2n`,
- random larger-speed probes:
  - `n=10,12,14,15`,

all found full base-fibre examples with minimum multiplicity `<= 2`, and no example with minimum multiplicity `>= 3`.

This is not a proof. But it is a materially better target than BF.1, because it survives the newly found large-speed counterexamples.

## 5. Revised transport picture

The updated hierarchy should be:

1. **local patcher geometry**
   - exact congruence description at `b_0`;
2. **base-fibre thinness**
   - not necessarily multiplicity `1`,
   - but plausibly multiplicity `<=2`;
3. **dynamic thinning**
   - if the base-fibre thin object has width `2`, then one coverer drops out after a bounded episode, creating a multiplicity-`1` stage;
4. **transport failure**
   - once the burden reaches multiplicity `1`, the previously identified migration machinery takes over.

So the all-branch structure is still transport-instability. What changed is only the correct thinness threshold at the base fibre.

## 6. Practical consequence

The theorem target should now be reformulated.

Do **not** aim next to prove BF.1.

Aim instead at one of:

- **BF.2:** base-fibre multiplicity `<=2` exists, or
- **DT.0:** even if every residue has multiplicity at least `2` at `b_0`, some residue becomes multiplicity `1` after finitely many initial effective changes.

The second version may be closer to the true transport statement, because it allows the thin object to emerge dynamically rather than demanding that it already be visible at `b_0`.
