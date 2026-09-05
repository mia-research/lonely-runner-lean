# Window-Crossing Principle for the Multi-11 Dynamic Case

**Date:** 2026-03-24  
**Status:** Higher-level analytic recast of the dynamic branching phenomenon.

---

## 1. The main idea

The branch tree is not the primary object.

What governs the dynamics is a finite chain of **macro staircase rungs**, and
each rung has a corresponding **recovery window** for its owner.

If a branch image stays inside that window, the rung survives.
If it leaves that window, the rung is lost.

This is the real analytic explanation behind the observed refinement vs.
destructive behavior.

---

## 2. Recovery windows

Suppose runner `r` is supposed to carry the orbit from the current macro stage
to the next checkpoint

```text
d = (11(j+1)+1)/(11r)
```

through its right-bad interval.

Then the **recovery window** for that rung is exactly

```text
I(r,j) = ((11j+10)/(11r), (j+1)/r).
```

For every `t in I(r,j)`, runner `r` is right-blocking and

```text
tau_r(t) = d.
```

So the owner recovers the rung precisely on that interval.

This gives a clean dichotomy:

> **Window-crossing principle.**
> Let `u` be a branch image produced from the previous macro stage.
>
> - If `u in I(r,j)`, then the owner `r` still recovers the same macro rung.
>   The branch is a refinement.
> - If `u notin I(r,j)`, then the owner `r` is no longer available to recover
>   that rung. The branch has crossed a recovery-window boundary, so that macro
>   rung is lost.

This is algebraic, not heuristic: it is just the exact formula for the
right-bad interval of runner `r`.

---

## 3. First applications

### 3.1 Why `19` is harmless at the `9`-rung

The macro rung

```text
6/55 -> 4/33
```

is carried by runner `9` on the window

```text
I(9,0) = (10/99, 1/9).
```

Now

```text
23/209 in (10/99, 1/9),
```

because

```text
10/99 < 23/209 < 1/9.
```

Hence runner `9` still recovers `4/33`.
This is exactly why

```text
6/55 -> 23/209 -> 4/33
```

is only a refinement branch.

By contrast,

```text
23/198 > 1/9,
```

so the `18`-branch image lies *outside* the `9`-window.
Runner `9` cannot recover the rung, and the orbit drops to the lower basin
`3/22` (proved analytically in Lemma D1 of
`lrc_n11_dynamic_basin_lemmas_v1.md`).

### 3.2 Why `16` repairs but `17` and `25` destroy

The macro rung

```text
4/33 -> 12/77
```

is carried by runner `7` on the window

```text
I(7,0) = (10/77, 1/7).
```

Now

```text
10/77 < 23/176 < 1/7,
```

so the `16`-image stays inside the `7`-window. Therefore `7` still recovers
`12/77`.

But

```text
23/187 < 10/77,
34/275 < 10/77,
```

so the `17`- and `25`-images lie below the `7`-window. The `7`-rung is lost,
and the orbit drops into the lower basin `3/22` (Lemmas D2 and D3 in
`lrc_n11_dynamic_basin_lemmas_v1.md`).

### 3.3 Why `20` is destructive in a different way

The macro rung

```text
12/121 -> 6/55
```

is carried by runner `10` on the window

```text
I(10,0) = (1/11, 1/10).
```

Now

```text
23/220 > 1/10,
```

so the `20`-image lies outside the `10`-window.
Runner `10` cannot recover `6/55`; that rung is skipped.

But `23/220` still lies in the basin of `4/33` (Lemma R0 of
`lrc_n11_dynamic_basin_lemmas_v1.md`), so the loss is not an immediate drop to
a lower basin. It is a loss of an **upper rung**.

This is why basin membership alone was not enough: the true invariant is the
ordered chain of recovery windows.

---

## 4. The greater explanation

The dynamic system has two scales:

- **macro scale:** the ordered staircase rungs and their recovery windows;
- **micro scale:** extra branch images inserted by substitute runners.

The micro dynamics matter only through one question:

```text
Does the branch image stay inside the current macro recovery window?
```

If yes, the macro rung survives.
If no, the macro rung is lost.

So the whole branch phenomenon is really an instance of:

> **ordered window crossing in a finite macro staircase.**

This is the higher-level object behind the computations.

---

## 5. What remains to finish the proof

The remaining analytic theorem should now be formulated as follows.

> **Macro Staircase Window Theorem (target form).**
> In the multi-`11` ILE dynamics, every branch image produced at a macro stage
> either:
>
> 1. stays inside the recovery window of the current rung, hence is a refinement;
>    or
> 2. crosses a recovery-window boundary, hence irreversibly loses that rung.

To finish the dynamic proof, one must:

1. identify the full finite macro staircase relevant below the dangerous zone;
2. list its recovery windows;
3. check that every competing branch image crosses one of these windows in the
   sense above.

At that point the branch tree disappears, because the dynamics has been reduced
to a finite ordered window system.
