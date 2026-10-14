# Slot-Economy Audit v2: What Survives and What Still Needs Proof

**Date:** 2026-03-24  
**Status:** Audit complete. The original `v1` slot-economy proof is **not yet valid as written**, but the dynamic front is still sharply reduced.

---

## 1. Executive summary

The current file

```text
lrc_n11_slot_economy_theorem_v1.md
```

contains a plausible theorem statement,

```text
T_ILE(S) <= t*(q) = (55q+1)/(121q),
```

where `11q` is the smallest multiple of `11` present, but the proof in `v1`
does **not** yet establish it.

Two concrete findings now separate cleanly:

1. **No counterexample to the theorem statement has been found.**
   In all tested families, the bound `T_ILE(S) <= t*(q)` still holds easily.

2. **The proof in `v1` fails.**
   The induction there is indexed by the 20-step staircase for `E_ext(q)`,
   but two-multiple configurations can have **more than 20 productive ILE
   advances** before witnessing. So the step-count induction does not cover
   all orbits.

The correct remaining dynamic task is therefore:

```text
replace the 20-step staircase induction by a genuine multi-11 envelope theorem.
```

The strongest current empirical candidate is much sharper:

> **Multi-11 empirical bound.**  
> If a configuration contains at least two multiples of `11`, then
>
> ```text
> T_ILE(S) <= 4/11
> ```
>
> in every tested family.

This is vastly stronger than what the Containment proof needs, since all
dangerous windows begin near `10/11`.

---

## 2. The exact flaw in `slot_economy_theorem_v1`

The proof in `v1` argues:

- after the `k`-th ILE step, the current time is `<= s_k`,
- where `s_0, ..., s_20 = t*(q)` is the 20-step staircase,
- hence the orbit terminates by `s_20`.

The missing justification is that **an arbitrary configuration may take more
than 20 productive advances** before witnessing.

So even if one proves

```text
t_k <= s_k   for k = 0,...,20,
```

that does **not** by itself control steps `k > 20`.

This is not a hypothetical issue. It really occurs.

---

## 3. Explicit 22-step counterexample to the 20-step proof strategy

Consider the configuration

```text
S = (1, 5, 8, 11, 14, 17, 18, 19, 20, 22).
```

It has **two multiples of 11** (`11` and `22`) and the ILE takes `22`
productive advances before witnessing:

```text
1/11
 -> 12/121        by 11
 -> 23/220        by 20
 -> 23/209        by 19
 -> 23/198        by 18
 -> 3/22          by 8
 -> 17/121        by 22
 -> 23/154        by 14
 -> 17/110        by 20
 -> 34/209        by 19
 -> 17/99         by 18
 -> 2/11          by 17
 -> 23/121        by 11
 -> 12/55         by 5
 -> 5/22          by 18
 -> 28/121        by 22
 -> 45/187        by 17
 -> 23/88         by 8
 -> 56/209        by 19
 -> 34/121        by 11
 -> 45/154        by 14
 -> 56/187        by 17
 -> 67/220        by 20
```

and `67/220` is a witness.

So the `v1` proof cannot be correct in its current form: the orbit is not
subsumed by a 20-step induction.

---

## 4. What *does* still look true

Although the `v1` proof fails, the theorem statement itself still looks very
plausible.

### 4.1 The original staircase bound still survives all tested families

For the families checked so far:

- smallest multiple `11`, extra multiples `22, 33`,
- smallest multiple `22`, extra multiples `33, 44`,
- smallest multiple `33`, extra multiples `44, 55`,

the exact ILE witness time always satisfies

```text
T_ILE(S) <= t*(q),
```

and in fact is much smaller.

### 4.2 A much stronger empirical bound appears to hold

Exhaustive searches over all `31,824` choices of seven additional non-multiples
from `2..20` for each of the three bases

```text
(1,11,22),   (1,22,33),   (1,33,44)
```

found **no** configuration with witness time exceeding

```text
4/11.
```

So the current strongest tested statement is:

> **Empirical Multi-11 Conjecture.**
> If a configuration contains at least two multiples of `11`, then
>
> ```text
> T_ILE(S) <= 4/11.
> ```

This is far stronger than needed for Containment, since

```text
4/11 << A_(m,1)_left ~ 0.90...
```

for every dangerous runner `11m`.

---

## 5. The current tested extremals

### 5.1 Best witness found in the small-pool two-multiple searches

For the exhaustive families above, the latest witness found was

```text
23/66 = 0.348484...
```

attained for example by:

```text
(1, 4, 5, 6, 7, 9, 10, 16, 11, 22),
(1, 4, 5, 6, 7, 9, 10, 16, 22, 33),
(1, 4, 5, 6, 7, 9, 10, 16, 33, 44).
```

The mechanism here is not the original 20-step staircase. Instead:

- `10` and `9` play the early staircase roles,
- `16` acts as the best substitute for the missing `8`,
- later `16` also acts as the best substitute for the missing `3`,
- the orbit still witnesses well before `4/11`.

### 5.2 Why this matters

This shows that the multi-11 regime has its own finite-state structure.
It is **not** simply the original single-11 staircase with one extra runner
ignored.

That is exactly why the old slot-economy proof fails: the extra `11`-multiple
creates new branches, but they still seem to terminate early.

---

## 6. The corrected proof target

The last dynamic theorem should now be reformulated as follows.

> **Target theorem (corrected dynamic bridge).**
> Suppose the speed set contains at least two multiples of `11`.
> Then the ILE witnesses by some absolute time `T_guard < 10/11`
> (ideally `T_guard = 4/11`).

This is enough to close the Containment gap, because all dangerous windows for
the runner `11m` lie far to the right:

```text
A_(m,1)_left = (110m+87)/(121m+99) > 0.90.
```

So **any** uniform bound such as

```text
T_ILE(S) <= 4/11
```

would completely settle the multi-11 case.

---

## 7. Best next analytic move

The proof no longer needs the exact extremal staircase `t*(q)`.

The most promising next move is:

1. Prove a coarse but universal theorem for the multi-11 regime, e.g.

```text
T_ILE(S) <= 4/11.
```

2. Do this by a **finite blocker-role analysis below `4/11`**:

- determine which runners can push the orbit from one sub-checkpoint to the
  next,
- identify the best substitutes (`16`, `19`, certain even `11`-multiples),
- show every branch below `4/11` terminates.

This is a substantially smaller and more realistic target than the old
`T_ILE <= t*(q)` theorem.

---

## 8. Bottom line

The original slot-economy theorem is **not yet proved**.

But the remaining gap is now much cleaner:

- the single-11 regime is governed by the 20-step staircase,
- the multi-11 regime appears to have its own finite-state early-termination
  mechanism,
- and all evidence says it terminates **far** before the dangerous zone.

So the dynamic front is not solved yet, but it is now reduced to one very
specific task:

```text
prove an early universal bound (preferably <= 4/11) for configurations with
at least two multiples of 11.
```
