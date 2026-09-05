# Dynamic Basin Lemmas for the Multi-11 Case

**Date:** 2026-03-24  
**Status:** First analytic basin lemmas proving the difference between
refinement branches and destructive branches.

---

## 1. The right object

The earlier branch analysis compared runners by their local late checkpoint
value `tau_p(t)`. That is too fine.

The correct object is the **basin** of a checkpoint.

> **Definition.**
> Let `c` be a staircase checkpoint.
> A time `u < c` lies in the basin of `c` if:
>
> 1. one of the staircase runners blocks at `u` with next-entry exactly `c`;
> 2. every blocking runner has next-entry `<= c`.

Then any branch landing in the basin of `c` is harmless for upper bounds: from
that point onward the ILE cannot outrun the orbit starting at `c`.

The analytic goal is therefore:

- prove that the `19`-branch lands in the basins of the same upper checkpoints;
- prove that the `17/18/25` branches land in the basin of the lower checkpoint
  `3/22`.

This file proves the first batch of those basin lemmas exactly.

We use the universal step-size bound from
`lrc_n11_dynamic_checkpoint_lemmas_v1.md`:

```text
tau_p(t) < t + 2/(11p)
```

for every blocking runner `p`.

---

## 2. Refinement basin lemmas for runner 19

Before treating the `19`-refinements, it is useful to record the first image of
the `20`-branch. It shows why basin membership alone is not enough: `20` does
not immediately fall into a *lower* basin, but it still skips an upper
checkpoint.

### Lemma R0. `23/220` lies in the basin of `4/33`

> Among all blocking runners at
>
> ```text
> t = 23/220,
> ```
>
> the largest next-entry time is
>
> ```text
> tau_max(23/220) = 4/33,
> ```
>
> attained by runner `9`.

**Proof.**

For `p >= 19`,

```text
tau_p(23/220) < 23/220 + 2/(11p) <= 23/220 + 2/209.
```

Since

```text
4/33 - (23/220 + 2/209) = 89/12540 > 0,
```

no `p >= 19` can beat `4/33`.

For `2 <= p <= 18`, the blocking runners are

```text
p = 9, 10, 18, 19.
```

Among those in range, only

```text
p = 9, 10, 18
```

occur, with

```text
tau_9(23/220)  = 4/33,
tau_10(23/220) = 6/55,
tau_18(23/220) = 23/198.
```

Since

```text
4/33 - 23/198 = 1/198 > 0,
4/33 - 6/55   = 2/165 > 0,
```

runner `9` is the maximizer. `square`

This shows that `20` does **not** immediately drop the orbit below the
`4/33`-basin. Its destructive effect comes from skipping the upper checkpoint
`6/55`, so a full theorem must track **basin depth**, not merely basin
membership.

---

### Lemma R1. `23/209` lies in the basin of `4/33`

> Among all blocking runners at
>
> ```text
> t = 23/209,
> ```
>
> the largest next-entry time is
>
> ```text
> tau_max(23/209) = 4/33,
> ```
>
> attained by runner `9`.

**Proof.**

For `p >= 19`, the step-size bound gives

```text
tau_p(23/209) < 23/209 + 2/(11p) <= 23/209 + 2/209.
```

Since

```text
4/33 - (23/209 + 2/209) = 1/627 > 0,
```

no `p >= 19` can beat `4/33`.

So only `2 <= p <= 18` need be checked directly.
The blocking runners in this range are:

```text
p = 9, 18,
```

with

```text
tau_9(23/209)  = 4/33,
tau_18(23/209) = 23/198.
```

Since

```text
4/33 - 23/198 = 1/198 > 0,
```

runner `9` is the maximizer. `square`

---

### Lemma R2. `34/209` lies in the basin of `2/11`

> Among all blocking runners at
>
> ```text
> t = 34/209,
> ```
>
> the largest next-entry time is
>
> ```text
> tau_max(34/209) = 2/11,
> ```
>
> attained by runner `6`.

**Proof.**

For `p >= 13`,

```text
tau_p(34/209) < 34/209 + 2/(11p) <= 34/209 + 2/143.
```

Since

```text
2/11 - (34/209 + 2/143) = 14/2717 > 0,
```

no `p >= 13` can beat `2/11`.

For `2 <= p <= 12`, the only blocking runners are

```text
p = 6, 12,
```

with

```text
tau_6(34/209)  = 2/11,
tau_12(34/209) = 23/132.
```

Since

```text
2/11 - 23/132 = 1/132 > 0,
```

runner `6` is the maximizer. `square`

---

### Lemma R3. `45/209` lies in the basin of `23/99`

> Among all blocking runners at
>
> ```text
> t = 45/209,
> ```
>
> the largest next-entry time is
>
> ```text
> tau_max(45/209) = 23/99,
> ```
>
> attained by runner `9`.

**Proof.**

For `p >= 15`,

```text
tau_p(45/209) < 45/209 + 2/(11p) <= 45/209 + 2/165.
```

Since

```text
23/99 - (45/209 + 2/165) = 46/9405 > 0,
```

no `p >= 15` can beat `23/99`.

For `2 <= p <= 14`, the only blocking runners are

```text
p = 5, 9, 14,
```

with

```text
tau_5(45/209)  = 12/55,
tau_9(45/209)  = 23/99,
tau_14(45/209) = 17/77.
```

Now

```text
23/99 - 17/77 = 8/693 > 0,
23/99 - 12/55 = 1/70 > 0,
```

so runner `9` is the maximizer. `square`

---

## 3. Destructive basin lemmas

These lemmas show that the dangerous substitute branches fall into the lower
basin of `3/22`, not the upper `16`-basin.

### Lemma D1. `23/198` lies in the basin of `3/22`

> Among all blocking runners at
>
> ```text
> t = 23/198,
> ```
>
> the largest next-entry time is
>
> ```text
> tau_max(23/198) = 3/22,
> ```
>
> attained by runner `8`.

**Proof.**

For `p >= 10`,

```text
tau_p(23/198) < 23/198 + 2/(11p) <= 23/198 + 1/55.
```

Since

```text
3/22 - (23/198 + 1/55) = 1/495 > 0,
```

no `p >= 10` can beat `3/22`.

For `2 <= p <= 9`, the blocking runners are

```text
p = 8, 9,
```

with

```text
tau_8(23/198) = 3/22,
tau_9(23/198) = 4/33.
```

Since

```text
3/22 - 4/33 = 1/66 > 0,
```

runner `8` is the maximizer. `square`

---

### Lemma D2. `23/187` lies in the basin of `3/22`

> Among all blocking runners at
>
> ```text
> t = 23/187,
> ```
>
> the largest next-entry time is
>
> ```text
> tau_max(23/187) = 3/22,
> ```
>
> attained by runner `8`.

**Proof.**

For `p >= 14`,

```text
tau_p(23/187) < 23/187 + 2/(11p) <= 23/187 + 1/77.
```

Since

```text
3/22 - (23/187 + 1/77) = 1/2618 > 0,
```

no `p >= 14` can beat `3/22`.

For `2 <= p <= 13`, the only blocking runner is

```text
p = 8,
```

and

```text
tau_8(23/187) = 3/22.
```

So runner `8` is uniquely maximal. `square`

---

### Lemma D3. `34/275` lies in the basin of `3/22`

> Among all blocking runners at
>
> ```text
> t = 34/275,
> ```
>
> the largest next-entry time is
>
> ```text
> tau_max(34/275) = 3/22,
> ```
>
> attained by runner `8`.

**Proof.**

For `p >= 15`,

```text
tau_p(34/275) < 34/275 + 2/(11p) <= 34/275 + 2/165.
```

Since

```text
3/22 - (34/275 + 2/165) = 1/1650 > 0,
```

no `p >= 15` can beat `3/22`.

For `2 <= p <= 14`, the only blocking runner is

```text
p = 8,
```

and

```text
tau_8(34/275) = 3/22.
```

So runner `8` is uniquely maximal. `square`

---

## 4. Interpretation

These lemmas give the first analytic proof of the branch dichotomy:

- the `19`-branch lands in upper basins (`4/33`, `2/11`, `23/99`);
- the `17/18/25` branches land in the lower basin `3/22`.

So the real difference is not merely that some runners branch earlier.
It is that:

```text
19  preserves the upper basin chain,
17/18/25 drop into a lower basin.
```

This is the first rigorous evidence for the proposed "staircase depth" /
"survival depth" mechanism.

---

## 5. What remains

To complete the analytic bridge, one still needs:

1. a formal definition of the coarse staircase depth;
2. a lemma showing that entering a lower basin strictly reduces the maximal
   attainable witness time;
3. a global theorem classifying all competing branches as either basin
   preserving or basin lowering.

But the key conceptual gap is now much smaller: we have exact analytic lemmas
showing that the important branch images already fall into two structurally
different classes.
