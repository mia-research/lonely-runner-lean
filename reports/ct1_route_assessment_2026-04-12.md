# CT.1 Route Assessment

Date: 2026-04-12
Status: diagnostic / next-step recommendation

## 1. Current theorem state

In [lrc_proof_v10_8.md](/Users/trentpalelei/Desktop/Math%20Ex/lrc_proof_v10_8.md), the prime dropped-unit branch now has:

- a correct actual-speed base-fibre description via Lemma 5.1a,
- a complete prime thinness lemma via Lemma 5.1b,
- and an open transfer theorem `CT.1`.

So the prime branch is no longer blocked at base-fibre thinness. It is blocked at the
post-transfer transport step.

## 2. The three candidate routes

The three routes currently on the table are:

- `A`: control or exclude the relevant simultaneous floor-reset events in the critical post-transfer interval;
- `B`: use the missing unit class `d notin R_non` to force eventual exposure of `r_d = -d^{-1}` or a residue tightly linked to it;
- `C`: use the terminal floor state near `b_max = (n-1)L/n`.

The question is not which route is prettiest in isolation. It is which route actually matches the observed mechanics of the prime branch.

## 3. Empirical comparison

### 3.1 Exhaustive prime scans already in scope

Using the existing bounded prime scans:

- `n=5`, speeds `<= 15`: `147` fully covered base-fibre tuples, all depth `0`.
- `n=7`, speeds `<= 14`: `420` fully covered base-fibre tuples, `416` depth `0`, `4` depth `1`, `0` depth `>1`.

For the `4` depth-`1` cases at `n=7`:

- there were **no coincident floor-reset events** in the critical interval after transfer and up to the first safe fibre;
- there were **no coincident floor-reset events at the safe event itself**;
- the first safe residue was **not** one of the canonical residues `r_d` attached to the missing unit class.

So the only genuinely difficult prime cases currently known are aligned with route `A`, not with a direct route `B` canonical-residue argument.

### 3.2 Random larger-prime probes

Random larger-prime sampling was also checked:

- `n=11`, speeds `<= 66`: `250` admissible sampled tuples with full analysis; all depth `0`.
- `n=13`, speeds `<= 78`: `200` admissible sampled tuples with full analysis; all depth `0`.

This does not prove anything, but it materially shifts the burden of proof:

- depth `1` already looks rare for larger prime `n`,
- depth `>1` remains unseen,
- and the observed safe fibres occur very early, not near the terminal end of the interval.

## 4. What this says about A/B/C

### Route A

This is currently the strongest route.

Why:

- it matches the actual obstruction named in the manuscript;
- it matches the older `M1` “coincident-boundary handling” bottleneck from the March geometry notes;
- it matches the only known prime depth-`1` cases;
- and it is compatible with the empirical fact that depth `1` is rare and depth `>1` is absent in all current scans.

The correct version of route `A` is probably **not**

> “simultaneous resets never occur,”

but rather

> “simultaneous resets cannot perform the needed repair in the critical post-transfer interval.”

That is narrower and much more believable.

### Route B

This is weaker as the main proof route.

Direct support is limited:

- `n=5` exhaustive scan: canonical safe residue hit in only `52/147` cases;
- `n=7` exhaustive scan: canonical safe residue hit in only `34/420` cases;
- among the `4` depth-`1` prime cases: canonical safe residue hit in `0/4`.

So route `B` may still be useful as a supporting invariant or bookkeeping tool, but it does **not** currently look like the main theorem path for `CT.1`.

### Route C

This is the weakest fit for the current structure.

Observed first safe fibres are typically early:

- average safe-position fraction `(b_safe-b_0)/(b_max-b_0)`:
  - `0.087` for exhaustive `n=5`,
  - `0.069` for exhaustive `n=7`,
  - `0.011` for random `n=11`,
  - `0.007` for random `n=13`.

So the prime branch does not currently behave like a terminal-fibre phenomenon. Route `C` may still encode a global consistency check, but it does not look like the natural first closure route for `CT.1`.

## 5. Best current formulation

The most promising next theorem target is therefore:

> **CT.1-A' (prime post-transfer non-repair theorem).**
> In the prime dropped-unit branch, let `r*` be a multiplicity-`1` residue at `b_0` with sole cover `e*`. If the first event dropping `r*` does not expose a safe fibre, then after the resulting transfer the companion residue cannot be repaired in the critical post-transfer interval before the first safe fibre appears.

This is deliberately weaker than a global “no coincidences” theorem. It only asks for what the proof actually needs.

## 6. Recommended next step

Do **not** spread effort equally across `A/B/C`.

The next proof pass should focus on route `A`, with the following tactical goal:

- isolate the exact arithmetic conditions under which a runner `f` could acquire the companion residue at a coincident event in the post-transfer interval;
- then prove those conditions are incompatible with the prime depth-`1` geometry.

Route `B` should be retained only as an auxiliary tracking invariant.
Route `C` should be treated as a fallback global perspective, not the main proof engine.
