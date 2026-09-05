# Dynamic Staircase Program for the `p_j = 11m` Containment Case

**Date:** 2026-03-24
**Status:** Strong exact reduction and extremal evidence; not yet a full proof.

This note records the strongest current understanding of the **dynamic**
remaining gap for the `n = 11` paper:

> prove Containment / ILE termination when the dangerous interior runner is
> `p_j = 11m`.

The main correction is that the right proof target no longer looks like
"preempt the earliest dangerous window near `10/11`." The ILE appears to
terminate far earlier, and the data point to a much more rigid **finite
staircase mechanism**.

---

## 1. The right extremal candidate

Among all tested configurations, the dynamically latest witness is produced by
the 8 small runners

```text
{3,4,5,6,7,8,9,10}
```

together with the dangerous runner `11m` and the slow runner `1`.

That is, the candidate extremal configuration is

```text
E_ext(m) = {1, 3, 4, 5, 6, 7, 8, 9, 10, 11m}.
```

For this configuration, the ILE is completely explicit and ends at

```text
t*(m) = (55m + 1)/(121m),
```

the **left endpoint of runner `11m`'s interval `I_(5m)^(m)`**.

Equivalently, the witness occurs at phase

```text
k = 5m.
```

This is exact for every tested `m`, and in fact the ILE trace is the same
finite staircase for all `m`.

---

## 2. Exact staircase for the candidate extremal configuration

For `E_ext(m)`, the ILE follows the same 20-step pattern for every `m >= 1`.

Starting from

```text
t_0 = 1/11,
```

the sequence is:

```text
1/11
 -> (11m+1)/(121m)          by 11m
 -> 6/55                    by 10
 -> 4/33                    by 9
 -> 3/22                    by 8
 -> 12/77                   by 7
 -> 2/11                    by 6

 -> (22m+1)/(121m)          by 11m
 -> 12/55                   by 5
 -> 23/99                   by 9
 -> 3/11                    by 4

 -> (33m+1)/(121m)          by 11m
 -> 23/77                   by 7
 -> 17/55                   by 10
 -> 4/11                    by 3

 -> (44m+1)/(121m)          by 11m
 -> 17/44                   by 8
 -> 23/55                   by 5
 -> 34/77                   by 7
 -> 5/11                    by 9

 -> (55m+1)/(121m)          by 11m,
```

and this final time is a witness.

For example:

```text
m=1:  t* = 56/121
m=2:  t* = 111/242
m=4:  t* = 221/484
m=8:  t* = 441/968
```

All satisfy `k = 5m`.

---

## 3. Exact computational evidence for extremality

### 3.1 Exhaustive search over small candidate pools

For `m = 2,3,4`, exhaustive search over all 8-subsets of

```text
{2,3,...,15} \ {11m}
```

gave a **unique** maximizer:

```text
{3,4,5,6,7,8,9,10}.
```

The maximum witness times were:

```text
m=2: 111/242
m=3: 166/363
m=4: 221/484
```

all matching `t*(m) = (55m+1)/(121m)`.

The same uniqueness held in the wider exhaustive search over all 8-subsets of

```text
{2,3,...,20} \ {11m}
```

for `m = 2,3`.

### 3.2 Random / hill-climb search with unrestricted integers

Targeted random search and crude hill-climbing over unrestricted integer speeds
(including much larger speeds, and including other multiples of 11) did **not**
find any configuration with witness time exceeding the staircase value.

In particular, forcing the defect-1 carrier `11m+9` into the configuration did
not push the ILE anywhere near the dangerous windows near `10/11`.

---

## 4. The finite-state comparison that now looks right

The best current proof program is:

> **Extremal Staircase Theorem (target).**
> For every configuration with dangerous runner `11m`, the ILE trajectory is
> bounded above by the staircase trajectory of `E_ext(m)`. Hence
>
> ```text
> t_witness <= (55m+1)/(121m),
> ```
>
> so the witness occurs by phase `k <= 5m`.

This would immediately imply Containment, because the dangerous windows begin
far later (near phase `k ~ 10m` and time `~ 10/11`).

The mechanism is no longer "top-window preemption." It is:

```text
all-orbits are trapped below the universal staircase envelope.
```

---

## 5. Why the staircase is plausible

At each staircase checkpoint, the delaying blocker is a **specific smallest
runner**:

```text
(11m), 10, 9, 8, 7, 6, (11m), 5, 9, 4, (11m), 7, 10, 3, (11m), 8, 5, 7, 9, (11m).
```

The computations show a robust pattern:

- the checkpoint blocker is the runner with the **largest next-entry time**
  among all blockers at that checkpoint,
- larger runners in the same role exist, but their next-entry times are smaller,
- if a required small runner is missing, the witness occurs earlier rather than
  later.

Examples from the exact scans:

- At `t = (11m+1)/(121m)`, runner `10` gives the largest non-dangerous next
  entry, namely `6/55`.
- At `t = 6/55`, runner `9` gives the largest next entry, namely `4/33`.
- At `t = 4/33`, runner `8` gives the largest next entry, namely `3/22`.
- At `t = 3/22`, runner `7` gives the largest next entry, namely `12/77`.
- At `t = 12/77`, runner `6` gives the largest next entry, namely `2/11`.

The same phenomenon repeats in later phases.

---

## 6. Important caveat: other multiples of 11

The staircase program is not yet a full proof.

The main extra complication is that other multiples of 11 can also block at the
pacemaker checkpoints `r/11`. For example, at `t = 2/11`, the smaller multiple
`11` has next entry `23/121`, which is larger than the dangerous runner's next
entry `(22m+1)/(121m)` when `m > 2`.

So the final theorem cannot simply ignore other `11`-multiples.

What **is** true empirically is that using a slot on such a runner appears to
force the loss of one of the critical small runners `{3,...,10}`, and this loss
causes an earlier witness rather than a later one.

So the real proof likely needs:

1. a one-step checkpoint lemma: at each staircase checkpoint, identify the
   runner with maximal next-entry time among all blockers;
2. a slot-economy lemma: replacing a required staircase runner by an additional
   multiple of 11 cannot increase the final witness time;
3. an induction showing the staircase envelope dominates every ILE orbit.

---

## 7. Current best dynamic theorem candidate

The cleanest corrected target is:

> **Dynamic Staircase Conjecture.**
> For every integer-speed configuration in the `p_j = 11m` case, the ILE finds a
> witness by the left endpoint of `I_(5m)^(m)`, i.e.
>
> ```text
> t_witness <= (55m+1)/(121m).
> ```
>
> Equality is attained exactly by the extremal staircase configuration
>
> ```text
> {1,3,4,5,6,7,8,9,10,11m}.
> ```

This is the strongest dynamic theorem currently supported by the exact data, and
it is much sharper than the older "preempt the earliest dangerous window"
formulation.
