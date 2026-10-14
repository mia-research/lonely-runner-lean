# `C_4` Exact Active-Core Reduction Note v1

## Purpose

This note exactifies the current `C_4` hard-case story for `n=11`.

It does **not** claim a complete final proof of the `n=11` Lonely Runner
Conjecture. What it does is:

1. replace float-scan `C_4` claims by exact `Fraction` certificates,
2. define the exact active-core notion on
   \[
   C_4=\left(\frac15,\frac14\right),
   \]
3. certify the exact finite folded object that every `C_4` argument must use,
4. certify the bounded `v_1=1`, speeds `<=17` full-`C_4` cases exactly,
5. record the two corrections forced by exactification:
   - minimal active cores are **not** exhausted by the old 6-runner picture,
   - a witness family does **not** depend on the minimal core alone.

The exact certifier for this note is
[lrc_c4_exact_active_core_certifier_v1.py](/Users/trentpalelei/Documents/Claude%20Library/lrc_c4_exact_active_core_certifier_v1.py),
with exact report
[lrc_c4_exact_active_core_certifier_report_v1.json](/Users/trentpalelei/Documents/Claude%20Library/lrc_c4_exact_active_core_certifier_report_v1.json).

The older synthesis note in `Math Ex` is now discovery background only.

---

## 1. Corridor normalization

Assume
\[
1=\lambda_1<\lambda_2<\cdots<\lambda_{10},
\qquad
\lambda_i=\frac{e_i}{e_1},
\qquad
x=e_1 t.
\]

On
\[
C_4=\left(\frac15,\frac14\right),
\]
runner `1` releases exactly the labels
\[
\{5,6,7,8,9,10\}.
\]

If some released label survives at some `x^* in C_4`, then the AP witness
\[
t^*=\frac{m^*x^*}{11e_1}
\]
is a lonely time.

So the full `C_4` problem is an exact covering problem for the released labels.

---

## 2. Exact folded algebra

Let
\[
F(y)=\min(y \bmod 11,\ 11-(y \bmod 11))
\in [0,11/2].
\]

For `a in [0,11/2]`, define the service state
\[
S(a)=\{m\in\{5,\dots,10\}:\{am/11\}\notin(1/11,10/11)\}.
\]

The exact folded partition has:

- `45` folded cells,
- `40` low-service cells with `|S|<=2`,
- `5` high-service cells with `|S|>=3`.

The exact active threshold on `C_4` is
\[
\lambda\ge \frac{40}{9}.
\]

Equivalently:

- if `lambda < 40/9`, then the runner is inactive on all of `C_4`,
- if `lambda >= 40/9`, then the runner is active somewhere on `C_4`.

This replaces the informal integer-only slogan “`lambda >= 5` active.”

The exact minimal abstract low-service cover counts are:

- size `3`: `9`,
- size `4`: `220`,
- size `5`: `117`,
- size `6`: `1`.

So the exact finite folded object is larger than the earliest graph summary,
but it is still genuinely finite.

---

## 3. Exact active-core definition

For a finite rational tuple `(\lambda_i)`, define the exact induced `x`-partition
of `C_4` by pulling back every folded cell boundary `beta` through
\[
F(\lambda_i x)=\beta.
\]

Equivalently, the partition cuts occur at exact rationals
\[
x=\frac{11k+\beta}{\lambda_i},
\qquad
x=\frac{11k-\beta}{\lambda_i},
\]
intersected with `C_4`.

On each open partition cell, every runner has constant folded state, hence
constant service state.

An **active full-cover subset** is a subset of the active runners whose union of
service states equals `\{5,6,7,8,9,10\}` on every cell of the induced partition.

A **minimal active core** is an inclusion-minimal active full-cover subset.

This is the exact object that replaces the old float-scan language “the active
set covers `C_4`.”

---

## 4. Exact finite results

### 4.1 Exact 6-runner catalogue up to `30`

The certifier proves exactly that the 6-runner active-core catalogue on
`\{5,\dots,30\}` is:

\[
\{5,6,7,8,9,10\},
\]
\[
\{5,6,7,8,10,18\},
\quad
\{5,6,7,9,10,16\},
\]
\[
\{6,7,9,10,14,16\},
\quad
\{6,7,9,10,16,19\},
\quad
\{6,7,9,10,16,24\}.
\]

There are exactly `6` such 6-runner full-cover sets up to `30`.

This exactifies the earlier discovery claim.

### 4.2 What this does **not** mean

The exact 6-runner catalogue is **not** the whole active-core story.

Bounded exact calibration already shows larger minimal active cores:

- `3` six-runner cores,
- `3` seven-runner cores,
- `12` eight-runner cores,

for a total of `18` exact minimal active-core signatures in the `v_1=1`,
speeds `<=17` calibration window.

So the correct theorem target is not “everything reduces to the six 6-runner
cores.” Those six are only the exact 6-runner layer.

---

## 5. Exact bounded calibration

On the exact finite testbed
\[
v_1=1,
\qquad
\{v_2,\dots,v_{10}\}\subset\{2,\dots,17\},
\]
the certifier proves:

- total `9`-subsets: `11,440`,
- exact full `C_4` cover subsets: `422`,
- exact `C_4` gap subsets: `11,018`,
- exact full `C_4` cover subsets containing `11`: `146`.

Moreover, every one of those `146` full-cover + `11` cases has an exact witness
\[
t=\frac{p}{q\cdot 11}
\]
with `q<=5`.

The exact first-witness distribution is:

- `t=1/11`: `276` cases,
- `t=7/22`: `99` cases,
- `t=3/22`: `20` cases,
- `t=9/22`: `9` cases,
- `t=8/33`: `8` cases,
- `t=16/33`: `7` cases,
- `t=21/44`: `2` cases,
- `t=13/55`: `1` case.

So the bounded witness claim survives exactification.

---

## 6. Two exact corrections

### 6.1 Minimal active cores can include `11`

The stronger heuristic

> “an active multiple of `11` cannot belong to a minimal active core”

is false.

Exact counterexample in the bounded calibration:
\[
\{2,5,7,8,9,10,11,12,13\}
\]
has exact minimal active core
\[
\{5,7,8,9,10,11,12,13\},
\]
which does contain `11`.

This configuration still has the exact witness
\[
t=\frac{7}{22}.
\]

So the right correction is:

- the exact 6-runner catalogue up to `30` contains no `11`,
- but larger minimal active cores with `11` do occur.

### 6.2 Minimal core alone does not determine the witness family

The stronger target

> “each minimal active core carries a universal rational witness family”

also fails in the bounded calibration, at least for the bounded family
\[
t=\frac{p}{q\cdot 11},
\qquad q\le 5.
\]

For every one of the `18` exact minimal active-core types in the bounded window,
the intersection of the bounded witness sets across all full tuples carrying that
core is empty.

So the witness depends on more than the minimal core alone.

This is the decisive correction from exactification: the correct remaining theorem
must be formulated at a finer level than minimal active core.

---

## 7. Exact consequences

What is now theorem-grade:

1. the exact active threshold `40/9`,
2. the exact folded finite object on `C_4`,
3. the exact definition of active full cover and minimal active core,
4. the exact 6-runner catalogue up to `30`,
5. the exact bounded calibration counts `422 / 146 / q<=5`,
6. the exact counterexamples to the two over-strong heuristic claims above.

What remains to finish the general `C_4` route:

1. identify the correct **full-cover signature** finer than minimal active core,
2. prove a witness theorem for that finer signature object,
3. show every exact full-cover configuration factors through one of those
   finitely many exact signatures.

In other words, the exactification pass succeeds, but it changes the target:

> the remaining theorem is a **signature-level witness theorem**, not a
> minimal-core witness theorem.

That is the right rigorous replacement for the earlier float-scan narrative.

---

## 8. Role of the discovery scripts

The float-driven file in `Math Ex` remains useful only for discovery:

- it suggested the active threshold,
- it suggested the 6-runner catalogue,
- it suggested small-denominator witnesses.

But no proof-critical claim in this note depends on float sampling.

All promoted claims are exact and are backed by
[lrc_c4_exact_active_core_certifier_v1.py](/Users/trentpalelei/Documents/Claude%20Library/lrc_c4_exact_active_core_certifier_v1.py).
