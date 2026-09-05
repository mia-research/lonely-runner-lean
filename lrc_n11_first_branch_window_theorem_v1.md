# First-Branch Window Theorem for the Multi-11 Dynamic Case

**Date:** 2026-03-24  
**Status:** First rigorous theorem showing that the greater explanation is
window crossing, not branch proliferation.

---

## 1. The theorem

Consider the macro staircase below the dangerous zone:

```text
12/121 -> 6/55 -> 4/33 -> 12/77 -> 2/11 -> 12/55 -> 23/99
       -> 3/11 -> 23/77 -> 17/55 -> 7/22 -> 39/121 -> 23/66.
```

The relevant owner recovery windows for the first nontrivial substitute stages
are:

```text
W_10 = (1/11, 1/10),
W_9  = (10/99, 1/9),
W_7  = (10/77, 1/7).
```

> **Theorem F1 (First-branch window classification).**
> At the first deviation from the macro staircase:
>
> 1. the runner `19` is the unique refinement branch among the first
>    non-staircase substitutes;
> 2. the runners `18,20,17,25` are destructive branches;
> 3. the distinction is exactly whether the branch image stays inside the next
>    owner recovery window.

In precise form:

```text
23/209 in W_9,
23/198 notin W_9,
23/220 notin W_10,
23/187 notin W_7,
34/275 notin W_7.
```

So the first branch is controlled entirely by ordered window crossing.

---

## 2. Proof

### Step 1. The `19`-branch is a refinement branch

At the first deviation point

```text
6/55,
```

runner `19` produces the branch image

```text
23/209.
```

Now

```text
10/99 < 23/209 < 1/9,
```

since

```text
23*99 - 10*209 = 187 > 0,
209 - 9*23 = 2 > 0.
```

Therefore

```text
23/209 in W_9 = (10/99, 1/9).
```

So the owner `9` remains right-blocking and still recovers the rung

```text
4/33.
```

Analytically, this is confirmed by Lemma R1 in
`lrc_n11_dynamic_basin_lemmas_v1.md`, which proves

```text
tau_max(23/209) = 4/33.
```

Hence the `19`-branch is a refinement branch.

---

### Step 2. The `18`-branch is destructive

At the same macro stage `6/55`, runner `18` produces

```text
23/198.
```

But

```text
23/198 > 1/9,
```

because

```text
9*23 - 198 = 9 > 0.
```

So

```text
23/198 notin W_9.
```

The `9`-rung is lost. Analytically, Lemma D1 in
`lrc_n11_dynamic_basin_lemmas_v1.md` shows that the orbit drops to

```text
tau_max(23/198) = 3/22,
```

not to `4/33`.

Thus `18` is a destructive branch.

---

### Step 3. The `20`-branch is destructive

At the earlier macro stage

```text
12/121,
```

runner `20` produces

```text
23/220.
```

Now

```text
23/220 > 1/10,
```

since

```text
10*23 - 220 = 10 > 0.
```

Therefore

```text
23/220 notin W_10 = (1/11, 1/10).
```

So the owner `10` can no longer recover the rung

```text
6/55.
```

This is the first instance showing that a branch may remain in an upper basin
while still being destructive: Lemma R0 in
`lrc_n11_dynamic_basin_lemmas_v1.md` proves

```text
tau_max(23/220) = 4/33,
```

so `20` does not immediately drop to a lower basin, but it **does** skip the
`10`-rung.

Thus `20` is destructive by window crossing at the `10`-stage.

---

### Step 4. The `17`- and `25`-branches are destructive

At the macro stage

```text
4/33,
```

the key substitute images are

```text
23/187   by 17,
34/275   by 25.
```

The next owner is runner `7`, whose recovery window is

```text
W_7 = (10/77, 1/7).
```

We claim both images lie below `10/77`.

For `23/187`:

```text
10/77 - 23/187 = (10*187 - 23*77)/(77*187) = 99/14399 > 0.
```

For `34/275`:

```text
10/77 - 34/275 = (10*275 - 34*77)/(77*275) = 132/21175 > 0.
```

Hence

```text
23/187, 34/275 notin W_7.
```

So the owner `7` cannot recover the rung

```text
12/77.
```

Analytically, Lemmas D2 and D3 in
`lrc_n11_dynamic_basin_lemmas_v1.md` show that both branches fall to

```text
tau_max = 3/22,
```

not to `12/77`.

Thus `17` and `25` are destructive branches.

---

## 3. Conclusion

The first branch phenomenon is not explained by the size of the substitute
runner or by the local late value of `tau`.

It is explained by a single algebraic principle:

> **A first branch is harmless exactly when its image remains inside the next
> owner recovery window.**

For the first nontrivial substitutes:

- `19` is harmless because `23/209 in W_9`;
- `18` is destructive because `23/198 > 1/9`;
- `20` is destructive because `23/220 > 1/10`;
- `17` and `25` are destructive because their images are below `10/77`.

So the branch structure is already collapsing at the first deviation:
the real object is an ordered system of recovery windows.

---

## 4. What this does and does not prove

This theorem does **not** yet prove the full dynamic case for `n = 11`.

What it proves is the first rigorous version of the greater explanation:

- the first substitute stage is finite and structural;
- its behavior is governed by exact window inequalities;
- the correct invariant is window preservation / window crossing, not a
  computational branch tree.

That is the right algebraic foundation for a genuinely noncomputational proof.
