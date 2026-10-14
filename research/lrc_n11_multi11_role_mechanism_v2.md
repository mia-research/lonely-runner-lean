# Multi-11 Dynamic Mechanism v2: Role-Ladder Deficit and Harmonic Substitutes

**Date:** 2026-03-24  
**Status:** Corrected mechanism note. Replaces the too-rigid "residue-budget" phrasing.

---

## 1. What was wrong with the first mechanism draft

The earlier mechanism note treated the multi-11 obstruction as if it were
controlled purely by the residue classes

```text
3,4,5,6,7,8,9,10 mod 11.
```

That is too rigid.

The actual traces show that a missing small blocker can often be replaced by a
larger **harmonic substitute** with a different residue mod `11`. For example:

- the role of `8` at `4/33` can be replaced by `16`,
- the role of `3` at `17/55` can also be replaced by `16`,
- the role of `9` at `6/55` can be replaced by `18`,
- the role of `10` at `23/77` can be replaced by `20`.

So the real mechanism is not "missing residue class." It is:

> **missing critical blocker role in the staircase ladder.**

The compensation comes from higher harmonics, not necessarily from the same
mod-`11` residue.

---

## 2. The correct object: the blocker-role ladder

Before `4/11`, the single-11 staircase is driven by the small-runner ladder

```text
10 -> 9 -> 8 -> 7 -> 6 -> 5 -> 4 -> 7 -> 10 -> 3.
```

Equivalently, the critical checkpoint blockers are:

```text
at 1/11 + 1/(121q):  10
at 6/55:             9
at 4/33:             8
at 3/22:             7
at 12/77:            6

at 2/11 + 1/(121q):  5
at 12/55:            9
at 23/99:            4

at 3/11 + 1/(121q):  7
at 23/77:            10
at 17/55:            3.
```

This is the ladder that must be sustained if the orbit is to stay late.

---

## 3. Why two multiples of 11 force a deficit

If the speed set contains at least two multiples of `11`, then among the ten
speeds:

- one slot is used by the slow runner `1`,
- at least two slots are used by multiples of `11`,
- so only **seven** slots remain for non-multiples.

But the late staircase depends on **eight** small-runner roles:

```text
3,4,5,6,7,8,9,10.
```

Therefore:

> **At least one critical ladder role must be absent.**

This is the real combinatorial obstruction.

Not every absent role is equally damaging, because some roles have strong
harmonic substitutes and others do not.

---

## 4. The substitute hierarchy

The traces reveal a clear "second-best blocker" hierarchy.

### 4.1 Strong substitutes

- `8` is best replaced by `16` at `4/33`:

```text
8  -> 3/22,
16 -> 23/176.
```

- `3` is best replaced by `16` at `17/55`:

```text
3  -> 4/11,
16 -> 7/22.
```

- `9` is best replaced by `18` at `6/55`:

```text
9  -> 4/33,
18 -> 23/198.
```

- `10` is best replaced by `20` at `23/77`:

```text
10 -> 17/55,
20 -> 67/220.
```

### 4.2 Interpretation

The multi-11 orbit survives by climbing a **weaker shadow ladder**:

```text
20, 19, 18, 17, 16, 14, ...
```

instead of the exact small-runner ladder.

So the right mental model is:

```text
exact ladder      vs.      harmonic substitute ladder.
```

Every time the orbit is forced onto the substitute ladder, the envelope drops.

---

## 5. The universal late endgame really does run through `16`

Although `16` is not the only substitute that appears, it does seem to control
the **late endgame**.

All the strongest currently known multi-11 examples eventually pass through:

```text
17/55 -> 7/22   by 16.
```

Examples:

### 5.1 Missing `3`

```text
(1,4,6,7,9,10,11,16,19,22)
```

Trace tail:

```text
... -> 23/77 -> 17/55 -> 7/22 -> 39/121 -> 23/66.
```

### 5.2 Missing `8`

```text
(1,4,6,7,9,10,11,14,16,22)
```

Trace tail:

```text
... -> 23/77 -> 17/55 -> 7/22 -> 39/121 -> 23/66.
```

### 5.3 Missing `9`

```text
(1,4,6,8,10,14,16,18,22,33)
```

This orbit uses the `18`-substitute earlier, but still ends by entering the
same `16`-endgame:

```text
... -> 17/55 -> 7/22 -> 39/121 -> 23/66.
```

So the corrected claim is:

> `16` is not the only substitute branch, but it appears to be the
> **universal late branch** once the orbit gets deep enough.

That is a more accurate statement than the earlier "best substitute branch is
the 16-branch" phrasing.

---

## 6. The strongest competing branch found so far

The strongest non-`16` near-extremal branch currently identified is the
missing-`4/10` branch, typified by

```text
(1,5,8,11,14,17,18,19,20,22),
```

with witness

```text
67/220.
```

Its late segment is driven by the substitute ladder

```text
20 -> 19 -> 18 -> 17
```

rather than by `16`.

So the hierarchy currently looks like:

```text
strongest late branch:     ... -> 16-endgame -> 23/66
next strongest branch:     ... -> 20/19/18/17 branch -> 67/220
all others:                earlier.
```

---

## 7. What the exhaustive scans say

For the three exhaustive bases

```text
(1,11,22),   (1,22,33),   (1,33,44),
```

the top deficit patterns were:

```text
missing (3), (8), (9), or (3,8)   -> max 23/66
missing (4,10) or (3,10)           -> max 67/220
missing (3,9)                      -> max 17/55
```

So the hierarchy above is not anecdotal; it is exactly what the exhaustive
searches are seeing.

---

## 8. The corrected "why"

The multi-11 case branches because the orbit is forced to solve two competing
problems at once:

1. **Pacemaker problem.**  
   Extra multiples of `11` create additional pacemaker moves.

2. **Role-budget problem.**  
   Those same extra multiples consume non-multiple slots, so some critical
   blocker role in the small-runner ladder must be absent.

The orbit survives by replacing missing ladder roles with harmonic substitutes.
But every replacement is weaker than the original role, so the envelope drops.

This is why:

- the exact single-11 staircase ceases to govern,
- the multi-11 orbits can be longer,
- yet they still terminate much earlier than the dangerous zone.

That is the actual causal mechanism.

---

## 9. The best next proof target

The most realistic theorem now seems to be:

> **Multi-11 substitute theorem.**
> In any configuration with at least two multiples of `11`, every ILE orbit
> eventually enters one of a small number of substitute branches.
> The strongest such branch is the `16`-endgame and terminates by
>
> ```text
> 23/66.
> ```
>
> The next strongest branch is the `20/19/18/17` branch and terminates by
>
> ```text
> 67/220.
> ```
>
> Hence
>
> ```text
> T_ILE(S) <= 23/66 < 4/11
> ```
>
> or at worst a slightly weaker uniform bound such as `4/11`.

Even if the exact `23/66` statement is still too ambitious, this mechanism is
now concrete enough to support a finite analytic branch proof below `4/11`.
