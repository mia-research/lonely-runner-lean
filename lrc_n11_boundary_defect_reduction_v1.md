# Boundary-Defect Reduction for the Remaining n=11 Gaps

**Date:** 2026-03-24
**Status:** Exact reductions proved; final universal bridge still open.

This note records the strongest analytic reductions currently justified for the
two remaining n=11 fronts, together with one important correction discovered
after the first draft:

1. Dynamic Containment for interior dangerous runners `p_j = 11m`.
2. Static Route 3 incompatibility for the terminal pair `(2,9)`.

The correction is that the naive universal sigma_2 = -1 "runner 9 must also
fail" theorem is false in that raw form. Runner 9 can geometrically overlap its
primary slot and the terminal slot `I_9` simultaneously in some classes; the
remaining static obstruction is therefore still class-conditional.

The central object is the **boundary defect**: a small deficit between the
numerator of a dangerous re-entry time and the top boundary `10/11`.

---

## 1. Correction: the scaled WITM statement is false

The blanket statement

```text
For every m >= 1 and every set S of at most 8 non-11 runners,
some scaled interval I_k^(m) has non-empty witness zone.
```

is false for `m = 6, 7, 8`.

Let

```text
I_k^(m) = [(11k+1)/(121m), (11k+10)/(121m)].
```

Exact witness-zone computation gives:

- `m = 6`: the set `{8, 9, 10}` fully blocks `I_6^(6), I_7^(6), I_8^(6)`.
- `m = 7`: the set `{9, 10}` fully blocks `I_7^(7), I_8^(7)`.
- `m = 8`: the runner `10` alone fully blocks `I_8^(8)`.

These are exact identities:

```text
m=6, p=10, k=6: 10*I_6^(6) = [335/363, 380/363]
m=6, p= 9, k=7:  9*I_7^(6) = [117/121, 261/242]
m=6, p= 8, k=8:  8*I_8^(6) = [356/363, 392/363]

m=7, p=10, k=7: 10*I_7^(7) = [780/847, 870/847]
m=7, p= 9, k=8:  9*I_8^(7) = [801/847, 126/121]

m=8, p=10, k=8: 10*I_8^(8) = [445/484, 245/242]
```

In each case, the mod-1 image lies entirely in
`[0,1/11) U (10/11,1)`, so the interval is fully blocked.

**Conclusion.** The remaining Containment problem cannot be closed by a purely
static "some scaled witness interval stays free" theorem. The correct theorem
must be dynamic: a **preemption theorem** for dangerous windows.

---

## 2. Dynamic side: exact dangerous-window classification

Fix an interior dangerous runner

```text
p_j = 11m,   m >= 1,
```

with dangerous zone

```text
D_(11m) = ((110m-1)/(121m), 10/11).
```

Suppose a runner `p > 11m` has a re-entry time

```text
tau = (11k+1)/(11p)
```

in `D_(11m)`. Define the **defect**

```text
d = 10p - (11k+1).
```

Then:

- `d` is a positive integer because `tau < 10/11`.
- `d < p/(11m)` because `tau > (110m-1)/(121m)`.
- `d == 10 - p (mod 11)` because `11k+1 == 1 (mod 11)`.

Equivalently:

> **Lemma D1 (Dangerous re-entry classification).**
> A re-entry time `(11k+1)/(11p)` lies in `D_(11m)` if and only if there exists
> an integer `d >= 1` such that
>
> ```text
> 11k+1 = 10p - d,
> d < p/(11m),
> d == 10 - p (mod 11).
> ```

This identifies every dangerous advance by a single arithmetic defect `d`.

---

## 3. Minimal dangerous carrier in each residue class

Fix a residue `r = p mod 11`.

The congruence `d == 10 - p (mod 11)` becomes

```text
d == 10 - r (mod 11).
```

The smallest positive defect compatible with `r` is:

- `d_r = 10 - r` for `r in {1,...,9}`,
- `d_10 = 11` for `r = 10`.

To realize defect `d_r`, we need `d_r < p/(11m)`, i.e.

```text
p > 11m d_r,
```

and `p == r (mod 11)`.

So the smallest dangerous runner in residue class `r` is

```text
p_min(m,r) = 11m d_r + r.
```

Explicitly:

```text
r=9  -> d=1  -> p_min = 11m + 9
r=8  -> d=2  -> p_min = 22m + 8
r=7  -> d=3  -> p_min = 33m + 7
...
r=1  -> d=9  -> p_min = 99m + 1
r=10 -> d=11 -> p_min = 121m + 10
```

This matches the exact searches:

- `m=1`: first dangerous runners are `20,30,...,100,131,...`
- `m=2`: first dangerous runners are `31,52,73,...,199,252,...`
- `m=6`: first dangerous runners are `75,140,205,270,...`

---

## 4. The earliest dangerous window is always defect 1

For a dangerous re-entry with defect `d`, the associated right-blocking approach
window is

```text
A_(p,d) = ((10p-d-2)/(11p), (10p-d-1)/(11p)).
```

For the minimal dangerous carrier of a given defect `d in {1,...,9}`, write

```text
p_d(m) = 11md + 10 - d.
```

Then the lower endpoint is

```text
L_d(m) = (10p_d - d - 2)/(11p_d)
       = 10/11 - (d+2)/(11p_d).
```

Since `p_d = d(11m-1) + 10`, define

```text
f_d(m) = (d+2)/p_d.
```

Direct subtraction gives

```text
f_(d+1) - f_d
= ((d+3)(d(11m-1)+10) - (d+2)((d+1)(11m-1)+10))
  / (((d+1)(11m-1)+10)(d(11m-1)+10))
= (12 - 22m) / denom
< 0
```

for every `m >= 1`.

Hence `f_d` is strictly decreasing, so `L_d` is strictly increasing in `d`.

Also the `r=10` class begins at defect `11`, which lies even further to the
right than the `d=9` window.

Therefore:

> **Lemma D2 (Earliest dangerous window).**
> Among all dangerous windows for `D_(11m)`, the leftmost one is always the
> defect-1 window, carried by residue `9`:
>
> ```text
> p_min = 11m + 9,
> A_(m,1) = ((110m+87)/(121m+99), (110m+88)/(121m+99)),
> tau_(m,1) = (110m+89)/(121m+99).
> ```

Examples:

```text
m=1: A_(1,1) = (197/220, 9/10),     tau = 199/220
m=2: A_(2,1) = (307/341, 28/31),    tau = 309/341
m=6: A_(6,1) = (249/275, 68/75),    tau = 749/825
```

**Reduction principle.** In any fixed configuration, let `d_*` be the smallest
defect realized by any dangerous carrier present. Since ILE times are monotone
increasing, the first dangerous window that can possibly be entered is the
leftmost realized one. So to rule out all dangerous windows, it is enough to
preempt the minimal-defect window.

This reduces the dynamic bridge to:

> **Open Dynamic Bridge.**
> Show that the minimal-defect dangerous window is always preempted.

---

## 5. Static side: runner 2 is eliminated in every sigma_2 = -1 class

Let `sigma_2 = -1`. Then runner 2 must close its primary slot `I_5` from below.

The slot `I_5 = [56/110, 65/110]` is covered by `B_(2,0)` exactly when

```text
10/(11 a_2) <= 56/110,
12/(11 a_2) >= 65/110.
```

This forces

```text
25/14 <= a_2 <= 24/13.
```

Now ask when runner 2 can cover the unclaimed slot

```text
I_9 = [10/11, 109/110].
```

The only possible bad intervals in the region `a_2 < 2` are:

- `B_(2,0)` reaches `I_9` when `a_2 in [100/109, 6/5]`,
- `B_(2,1)` reaches `I_9` when `a_2 in [210/109, 2)`,
- `B_(2,j)` for `j >= 2` never reaches `I_9` with `a_2 < 2`.

Therefore:

```text
[25/14, 24/13]  cap  [100/109, 6/5]  =  empty,
[25/14, 24/13]  cap  [210/109, 2)    =  empty.
```

The decisive gap is

```text
210/109 - 24/13 = 114/1417 > 0.
```

So:

> **Lemma S1 (Runner-2 elimination in sigma_2 = -1 classes).**
> In every sign class with `sigma_2 = -1`, runner 2 cannot simultaneously satisfy
> its primary obligation at `I_5` and absorb the unclaimed slot `I_9`.
>
> Equivalently: runner 2 is not the terminal absorber in any `sigma_2 = -1` class.

This is the static analogue of the dynamic defect reduction: the boundary defect
survives past runner 2 and is pushed onto the terminal pair `(2,9)`.

The remaining static bridge is:

> **Open Static Bridge.**
> Determine the exact class-conditional cascade constraint on runner 9 once
> runner 2 is eliminated. A universal runner-9 incompatibility theorem is false.

### Correction: the naive universal runner-9 theorem is false

The statement

```text
Once runner 2 is eliminated in sigma_2 = -1 classes, runner 9's primary window
and its I_9 window are automatically incompatible.
```

is false as stated.

Indeed, runner 9 can simultaneously overlap a primary-type interval near `I_4`
and the terminal slot `I_9`.

Take

```text
a_9 = 25/3.
```

Then:

```text
B_(9,3) = [43/(11 a_9), 45/(11 a_9)] = [129/275, 135/275]
```

which overlaps

```text
I_4 = [45/110, 54/110]
```

since

```text
129/275 < 54/110 = 135/275.
```

At the same time

```text
B_(9,7) = [87/(11 a_9), 89/(11 a_9)] = [261/275, 267/275]
```

overlaps

```text
I_9 = [10/11, 109/110].
```

More generally, solving the overlap inequalities shows:

- runner 9 overlaps `I_4` via `B_(9,3)` and `I_9` via `B_(9,7)` throughout

```text
a_9 in [870/109, 89/10] = [7.981651..., 8.9],
```

- and similarly overlaps `I_5` and `I_9` on non-empty ranges.

So the static frontier is NOT a universal runner-9 incompatibility theorem.
What remains open is the cascade-sensitive theorem: after the outer pairs fix the
leftover gap geometry, runner 9 may still be forced into an incompatible pair of
obligations, but this depends on the class-specific cascade.

---

## 6. Final reduced frontier

The remaining n=11 proof frontier is now concentrated in two exact bridges.

### Dynamic bridge

For each interior dangerous runner `p_j = 11m`:

1. dangerous right-blocking windows are classified exactly by defects `d`,
2. the leftmost dangerous window is always the defect-1 / residue-9 window,
3. it remains to prove that this earliest dangerous window is always preempted.

However, the current numerical evidence suggests an even stronger reformulation:
the ILE appears to terminate far below every dangerous window.

### Dynamic strengthening suggested by the traces

Targeted ILE searches with the defect-1 carrier `11m+9` forced into the
configuration never came remotely close to the left edge of `A_(m,1)`.

For `m = 2,...,8`, random sweeps with the carrier `11m+9` present gave:

```text
m=2: best t_max ≈ 0.155844
m=3: best t_max ≈ 0.136364
m=4: best t_max ≈ 0.141414
m=5: best t_max ≈ 0.137799
m=6: best t_max ≈ 0.139350
m=7: best t_max ≈ 0.137799
m=8: best t_max ≈ 0.141649
```

whereas

```text
A_(m,1) starts near 0.90 for every m.
```

A crude hill-climb designed to maximize the actual ILE witness time pushed the
worst observed witnesses only to:

```text
m=2: 0.234266
m=3: 0.228739
m=4: 0.349650
m=5: 0.140592
m=6: 0.158578
m=7: 0.195986
m=8: 0.166234
```

Moreover, if `k_w` denotes the dangerous runner's interval index of the witness,
all observed extremals satisfied

```text
k_w <= 4m - 1.
```

This suggests the real dynamic theorem is likely:

> **Open Dynamic Bridge (sharpened).**
> Prove that the ILE always finds a witness in one of the first `4m`
> isolation intervals of runner `11m`.

Such a theorem would make all dangerous windows irrelevant, since the top
boundary windows lie near the final phase `k ≈ 10m`.

### Static bridge

For Route 3:

1. `I_9` is the unclaimed boundary defect,
2. in `sigma_2 = -1` classes, runner 2 is analytically eliminated,
3. it remains to prove that runner 9 cannot absorb the residual defect either.

---

## 7. Interpretation

The branch structure is not accidental. In both settings, the system reduces to a
single unsatisfied boundary obligation:

- **Dynamic face:** a minimal positive defect `d = 1` trying to force a dangerous
  re-entry.
- **Static face:** an unclaimed terminal slot `I_9` trying to force an extra
  coverage obligation onto the terminal pair.

The universal theorem to be proved is therefore not "all cases separate nicely",
but two different corrected statements:

> **Dynamic face.**
> The ILE reaches a witness before the boundary defect can migrate to the top
> phase.

> **Static face.**
> After runner 2 is eliminated in sigma_2 = -1 classes, the remaining terminal
> obstruction is cascade-sensitive and must be proved with the actual leftover
> gap geometry; it does not collapse to a universal runner-9 incompatibility
> theorem.
