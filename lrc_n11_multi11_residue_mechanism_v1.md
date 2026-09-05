# Multi-11 Dynamic Mechanism: Residue-Budget Deficit

**Date:** 2026-03-24  
**Status:** Mechanism note. Explains *why* the multi-11 regime witnesses early.

---

## 1. Core diagnosis

The multi-11 case is **not** governed by the exact 20-step single-pacemaker
staircase. The extra multiples of `11` create new pacemaker resets and can
produce longer ILE orbits.

But the data strongly suggest that the real mechanism is simpler:

> **Residue-budget deficit.**  
> To delay the ILE deep into the window, one needs blockers from many residue
> classes mod `11`. With at least two multiples of `11` present, only seven
> non-multiple slots remain, so at least one of the crucial residue classes is
> absent. The orbit can partially compensate using second-best substitutes, but
> eventually the missing residue forces an early witness.

So the reason the multi-11 case still terminates early is not that the extra
`11`-multiple is harmless. It is that the extra `11`-multiple **costs a residue
slot**, and that loss is more important than the extra pacemaker delay it adds.

---

## 2. The single-11 reference: eight residue roles before `4/11`

In the single-11 staircase, the delaying blockers up to `4/11` use the residue
classes

```text
10, 9, 8, 7, 6, 5, 4, 3.
```

Concretely, the exact staircase from the checkpoint lemmas is:

```text
1/11 + 1/(121q)   -> 6/55      by residue 10
6/55              -> 4/33      by residue 9
4/33              -> 3/22      by residue 8
3/22              -> 12/77     by residue 7
12/77             -> 2/11      by residue 6

2/11 + 1/(121q)   -> 12/55     by residue 5
12/55             -> 23/99     by residue 9
23/99             -> 3/11      by residue 4

3/11 + 1/(121q)   -> 23/77     by residue 7
23/77             -> 17/55     by residue 10
17/55             -> 4/11      by residue 3.
```

So by the time the single-11 staircase reaches `4/11`, every residue class

```text
3,4,5,6,7,8,9,10
```

has become relevant.

This is the key structural fact.

---

## 3. Why multi-11 changes the game

If the speed set contains at least two multiples of `11`, then among the ten
speeds:

- one slot is occupied by the slow runner `1`,
- at least two slots are occupied by `11`-multiples,
- hence only **seven** slots remain for non-multiples.

So it is impossible to realize all eight residue classes

```text
3,4,5,6,7,8,9,10
```

simultaneously.

This forces a **deficit**:

```text
at least one crucial residue is missing.
```

That is the underlying reason the multi-11 regime cannot reproduce the full
single-11 staircase out to `4/11` and beyond.

---

## 4. What the exhaustive scans say

For each of the bases

```text
(1,11,22),   (1,22,33),   (1,33,44),
```

I exhaustively checked all `31,824` choices of seven additional non-multiples
from `2..20`.

The latest witnesses found were:

```text
23/66 = 0.34848...
```

and no configuration exceeded

```text
4/11 = 0.36363...
```

More importantly, the near-extremals are highly structured.

### 4.1 For base `(1,11,22)`

The latest residue-deficit patterns were:

```text
missing (3,8)   -> max witness 23/66
missing (8)     -> max witness 23/66
missing (3)     -> max witness 23/66
missing (4,10)  -> max witness 67/220
missing (3,10)  -> max witness 67/220
missing (3,9)   -> max witness 17/55
```

### 4.2 For base `(1,22,33)` and `(1,33,44)`

The same pattern reappears:

```text
missing (3,8)   -> max witness 23/66
missing (8)     -> max witness 23/66
missing (3)     -> max witness 23/66
missing (9)     -> max witness 23/66
missing (3,9)   -> max witness 17/55
```

So the late branches are not arbitrary. They come from a very small number of
least-harmful residue deficits.

---

## 5. Why residues `3` and `8` are the least harmful deficits

The reason the missing-residue patterns `(3)`, `(8)`, and `(3,8)` are the
latest is that they admit the best **second-best substitute**:

```text
residue 5, via the speed 16 ≡ 5 (mod 11).
```

Two exact examples:

### 5.1 At `t = 4/33`

The ideal blocker is residue `8`:

```text
8  -> 3/22.
```

But the next-best substitute is:

```text
16 -> 23/176.
```

So if residue `8` is missing but `16` is present, the orbit can still survive
past `4/33`, though not as long as in the exact staircase.

### 5.2 At `t = 17/55`

The ideal blocker is residue `3`:

```text
3 -> 4/11.
```

But the next-best substitute is again:

```text
16 -> 7/22.
```

So `16` is the best available stand-in for **both** of the fragile residue
roles `8` and `3`.

This is why the worst multi-11 examples almost always feature `16`.

---

## 6. Why the orbit still dies before `4/11`

The substitute `16` is good, but not good enough.

When the orbit uses `16` instead of residue `3`, it gets diverted to

```text
7/22
```

instead of

```text
4/11.
```

From there, the best available continuations are strictly weaker:

- with a smaller multiple of `11` present, the pacemaker can move to times like
  `39/121`,
- residue `6` can then push to `23/66`,
- but the orbit no longer has access to the exact residue-`3` bridge needed to
  reach `4/11`.

So the substitute buys time, but it also traps the orbit in a weaker side
branch.

That is why the near-extremal multi-11 orbits top out at

```text
23/66
```

instead of reaching the single-11 bound `t*(q)`.

---

## 7. Why some deficits are much worse

Missing residues like

```text
4, 9, 10
```

are more damaging because they do not have an equally strong universal
substitute.

Examples from the scans:

```text
missing (4,10)  -> 67/220
missing (3,10)  -> 67/220
missing (3,9)   -> 17/55
```

So the residue-deficit principle is not merely a counting heuristic. Different
missing residues have different severity, and the exhaustive data reveal a
clear hierarchy:

```text
least harmful:   3 and 8
moderately bad:  9
more harmful:    4 and 10
```

This matches the observed substitute behavior: `16` offers a strong fallback
for `3` and `8`, but there is no comparably effective fallback for the more
rigid `4/10` bridge.

---

## 8. The corrected conceptual theorem

The right conceptual statement now looks like this:

> **Multi-11 residue-deficit principle.**
> In any configuration with at least two multiples of `11`, the non-multiple
> runners realize at most seven of the eight critical residue roles
> `3,4,5,6,7,8,9,10`.
> The ILE can partially compensate by using second-best substitutes
> (especially residue `5` via `16`), but every such compensation lowers the
> eventual envelope. Therefore the orbit witnesses strictly before the full
> single-11 staircase would.

This explains:

- why the exact 20-step single-11 staircase no longer governs the proof,
- why the multi-11 regime still terminates early,
- why `16` appears repeatedly in the worst multi-11 examples,
- why the late multi-11 witnesses cluster around `23/66` rather than near
  `t*(q)`.

---

## 9. Best next proof target

The residue-budget mechanism suggests a more realistic theorem than the old
slot-economy statement:

> **Target theorem.**
> If a configuration contains at least two multiples of `11`, then
>
> ```text
> T_ILE(S) <= 4/11.
> ```

To prove this, it should be enough to:

1. classify the best substitute blockers for the missing residue roles,
2. show the strongest substitute branch is the `16`-branch,
3. prove that every such branch terminates by `23/66 < 4/11`.

If that is done, the multi-11 case is finished analytically, and the dangerous
window near `10/11` is no longer relevant.
