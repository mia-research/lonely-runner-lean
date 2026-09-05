# Dropped-Unit Repair Scan

Date: 2026-04-12
Status: bounded diagnostic note

## 1. Goal

Test the provisional repair idea suggested by the affine-shadow analysis:

> if a missing unit target is patched at the base fibre `b_0 = L/n`, then the patching runner should later encounter a forced handoff problem that creates a safe fibre.

The point of the scan was not to certify a theorem, but to determine whether this is the right repair shape for the dropped-unit gap in the all-`n` manuscript.

## 2. Exact algebraic fact: the right local object is a patching runner

Let `d` be a missing unit residue class and define the canonical target

`r_d = -d^{-1} mod n`.

Let `e = nq + rho` be an actual retained non-divisible speed. At the base fibre `b_0 = L/n`, one has

`floor(e b_0 / L) = q`,

so `e` blocks `r_d` iff

- `rho r_d + q ≡ 0 (mod n)`, or
- `rho r_d + q + 1 ≡ 0 (mod n)`.

Since `r_d = -d^{-1}`, this is equivalent to

- `rho ≡ q d (mod n)`, or
- `rho ≡ (q+1)d (mod n)`.

This is the exact local description of **every runner that patches the missing target at the base fibre**, whether `rho` is a unit or a non-unit.

So the unit-only “affine shadow” picture was already part of a broader mechanism:

**base-fibre patching is affine in `(q,rho)` for both unit and non-unit runners.**

## 3. Exhaustive scan scope

I used:

- [test_affine_shadow_repair.py](/Users/trentpalelei/Desktop/Math%20Ex/tools/test_affine_shadow_repair.py)
- [test_patching_runner_scan.py](/Users/trentpalelei/Desktop/Math%20Ex/tools/test_patching_runner_scan.py)
- [inspect_dropped_unit_instance.py](/Users/trentpalelei/Desktop/Math%20Ex/tools/inspect_dropped_unit_instance.py)

The exhaustive patching-runner scan covered all `Case 2` tuples with `gcd(E)=1`, at least one speed divisible by `n`, and speed ranges:

- `n=4,5,6` with speeds in `[1,3n]`,
- `n=7,8` with speeds in `[1,2n]`.

These are bounded diagnostics only, not proof.

## 4. Scan results

### 4.1 Exact patcher congruence

In every scanned instance, every runner that covered `r_d` at `b_0` satisfied the exact congruence

- `rho ≡ q d (mod n)`, or
- `rho ≡ (q+1)d (mod n)`.

There were no exceptions in the scan.

### 4.2 The first strong repair guess was too strong

The first guess was:

> if `r_d` is patched at `b_0`, then some patching runner later has a safe reset, and this is the right universal repair theorem.

This performed very well, but not perfectly:

- `n=4`: `6/6`
- `n=5`: `226/226`
- `n=6`: `828/828`
- `n=7` with speeds `<= 2n`: `663/663`
- `n=8` with speeds `<= 2n`: `1762/1764`

So the patcher-reset theorem is **almost right in bounded data, but not literally true as stated**.

### 4.3 The first safe fibre often appears elsewhere

Even in cases where a patching runner later has a safe reset, the **first** safe fibre often appears at a different event. The scan statistic

`first safe b is a patcher reset`

was:

- `n=4`: `6/6`
- `n=5`: `130/226`
- `n=6`: `498/828`
- `n=7` with speeds `<= 2n`: `151/663`
- `n=8` with speeds `<= 2n`: `517/1764`

So the missing-unit repair is not naturally a “first bad event belongs to the shadower” theorem.

## 5. The two informative outliers

The two bounded outliers at `n=8` were:

- `E=(2,8,10,11,12,13,14)`, missing unit `d=1`
- `E=(2,10,11,12,13,14,16)`, missing unit `d=1`

In both:

- the canonical target is `r_d = 7`,
- the unique base-fibre patcher is `e=10 = 8 + 2`,
- the patching congruence is the `rho ≡ (q+1)d` branch,
- but no later reset of `10` is safe.

Yet a safe fibre still appears later.

For

`E=(2,8,10,11,12,13,14)`

the first safe fibre is at

`b = 25740`,

which is a reset of `14`, not of `10`, and the missing residue is

`5`,

not the canonical target `7`.

So the lesson is sharp:

**patching the canonical dropped-unit target can force a later gap at a different residue and a different runner’s reset.**

That is why the first repair guess fails on these outliers without undermining the broader mechanism. A fuller prototype analysis appears in [n8_outlier_release_mechanism_2026-04-12.md](/Users/trentpalelei/Desktop/Math%20Ex/reports/n8_outlier_release_mechanism_2026-04-12.md): after removing divisible speeds the two outliers are the same `E_non` configuration, and the burden migrates from the canonical target `7` to the companion residue `5` before being released by runner `14`.

## 6. What the scan does support

The scan supports the following more careful picture.

### 6.1 What survives

- The old Sole Cover step was genuinely too crude.
- The real local object is an actual-speed patching runner `e = nq + rho`.
- Missing-unit patching is governed by an exact affine congruence in `(q,rho)`.
- This mechanism is not accidental; it appears in both unit and non-unit regimes.

### 6.2 What has to be weakened

The statement

> every affine shadow has its own forced handoff problem

is too narrow.

It should be weakened to something closer to:

> if the canonical dropped-unit target is patched at `b_0`, then the resulting affine patching burden cannot be transported through the whole divisible window without failure; however the eventual safe fibre need not occur at the patcher’s own reset and need not expose the original canonical target.

That is a substantially better repair target.

## 7. Best current theorem shape

The best current candidate is therefore not a one-runner theorem but a transport theorem:

> **Dropped-unit transport instability.**  
> If a unit residue class `d` is missing from the retained support, then either a safe fibre already exists near the base fibre, or the canonical target `r_d` is patched by one or more affine patching runners. In the latter case, the induced patching burden cannot be maintained throughout `B_div`; a later safe fibre must appear, though not necessarily at a reset of the original patcher and not necessarily at the residue `r_d`.

This is still a proof target, not yet a proved theorem.

## 8. Practical conclusion for the manuscript

The repair programme should not aim to prove

> missing unit => immediate miss at `r_d`,

or even

> missing unit => patcher reset exposes `r_d`.

The scan says the right target is broader:

> missing unit => patching burden is globally unstable.

That is much closer to the true geometry of the bounded exceptions.
