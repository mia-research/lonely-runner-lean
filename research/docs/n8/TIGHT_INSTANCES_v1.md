# The extremal boundary at n=8 — three tight instances, and what they break

2026-09-07. New object; supersedes nothing. Artifacts:
`experiments/n8/{tight_sets_v2, tight_sets_gen_v1, pacemaker_n8_v1, pacemaker_n8_v2}.py`.
Grade authority for `docs/n8/` remains `CLAIM_GRADES_v1.md`; the grades below are
this file's own.

A **tight instance** at `n = 8` is a set `T` of 7 distinct positive integers,
`gcd(T) = 1`, with `M(T) := max_t min_{v∈T} ‖v t‖ = 1/8` exactly. LRC(8) gives
`M(T) ≥ 1/8`, so the tight instances are the boundary any proof must be sharp
against. They had not been computed in this corpus.

## 1. The witness ladder splits n=8 into two cases, and only one is tight

**`[PROVED]`** For `q ∈ {2,…,8}` and `gcd(a,q)=1`, `‖v·a/q‖ = |va mod q|/q ≥ 1/q`
whenever `q ∤ v`. So:

- `q ≤ 7`: if `q` divides no speed, `t = a/q` gives `M(T) ≥ 1/q > 1/8` — **strictly**.
- `q = 8`: if 8 divides no speed, `t = m/8` (`m` odd) gives `M(T) ≥ 1/8` — **tightly**.

Maximal levels are `q = 5, 6, 7, 8`. Hence the **residual case** — the only one
needing an argument — is `T` containing a multiple of 5, of 6, of 7 **and of 8**.
Everything else is one line. This is the `q = 8` rung of the ladder already recorded
in `N11_TRANSLATION_v1.md` §3; what is new is that `q = 8` is the *equality* rung,
so the split above is exactly a split into "tight" and "not tight".

## 2. The three tight instances  `[EMPIRICAL — exhaustive over speeds ≤ 24]`

Exhaustive over all 7-subsets of `{1,…,24}` with `gcd = 1` passing the ladder filter
(111 409 sets). Exact rational arithmetic; no floating point in any decision.

| `T` | `e_max/e_min` | `a_1 = 7e_1/e_7` |
|---|---|---|
| `{1,2,3,4,5,6,7}` (the AP) | 7 | `1` — bounded ratio |
| `{1,2,3,4,5,7,12}` | 12 | `7/12 < 1` — large ratio |
| `{1,4,5,6,7,11,13}` | 13 | `7/13 < 1` — large ratio |

Verified by two independent exact methods: interval-coverage sweep
(`tight_sets_v2.py`) and global crossing enumeration over all
`t = k/(2v_i), k/(v_i±v_j)`. Both return `M = 1/8`.

**Scope.** `≤ 24` only. This is not a classification; a sweep to `≤ 34` was running
when this file was written and is recorded as owed.

## 3. All three are tight for the same reason  `[VERIFIED-INSTANCE]`

Their good sets — computed exactly, not sampled — are **identical**:

    { t : min_v ‖v t‖ = 1/8 }  =  {1/8, 3/8, 5/8, 7/8}   for all three.

and **none of the three contains a multiple of 8**. So all three are tight for the
`q = 8` reason of §1 and nothing else: the witness is the unit witness, the value is
`1/8`, and no better `t` exists anywhere.

At each witness `‖v·m/8‖` depends only on `v mod 8` — `0 → 0`, `±1 → 1/8`,
`±2 → 1/4`, `±3 → 3/8`, `4 → 1/2` — so a single speed divisible by 8 kills all four
witnesses at once, and no speed divisible by 8 leaves all four alive.

**Consequence, and it is the useful one.** The tight instances all lie *outside* the
residual case of §1. The residual case is therefore **not tight** on the evidence so
far: `min M` over residual sets with speeds `≤ 32` was `2/15 ≈ 0.1333` when this file
was written (run incomplete, recorded as owed) against `1/8 = 0.125`.
`[EMPIRICAL, scope = the stated range; NOT a gap theorem]`

## 4. What this breaks: the n=11 architecture's target statement  `[PROVED]`

`eleven_lonely_runners_v33.md` proves LRC(11) by showing
`GF(I_k) > 0` for some pacemaker slot in every completely blocking configuration
(`:761-762`, Theorem 7.3), where `GF` is the **Lebesgue** good fraction (`:174-175`).
It excludes the AP by hand: `:187-188` — *"We exclude the measure-zero hyperplanes
$a_j=j$"*.

Translated to `n = 8` (`pacemaker_n8_v2.py`; `a_i = 7e_i/e_7`, `a_7 = 7`,
`B_{j,k} = [(8k+7)/(8a_j), (8k+9)/(8a_j)]`, `I_s = [(8s+1)/56, (8s+7)/56]`,
`W_ref = [1/(8a_1), 7/(8a_1)]`), the two non-AP tight instances are **completely
blocking with `GF(I_s) = 0` in every slot of `W_ref`**:

- `{1,2,3,4,5,7,12}` → `a = (7/12, 7/6, 7/4, 7/3, 35/12, 49/12, 7)`; all **10** slots
  in `W_ref = [3/14, 3/2]` fully covered.
- `{1,4,5,6,7,11,13}` → `a = (7/13, 28/13, 35/13, 42/13, 49/13, 77/13, 7)`; all **11**
  slots in `W_ref = [13/56, 13/8]` fully covered.

and **neither lies on a hyperplane `a_j = j`** — every coordinate above differs from
its index. The AP-hyperplane exclusion does not reach them.

So at `n = 8` the statement *"every completely blocking configuration has a slot with
positive good fraction"* is **false**, with two explicit witnesses. The Lebesgue good
fraction is the wrong functional: for a tight instance the good set is a nonempty
**finite** set of points, so `GF = 0` while LRC still holds. The correct target is the
open-interval statement — *the open bad intervals leave a point uncovered* — which the
touch-point structure carries and `GF` discards.

**This is not a defect found in v33; it is a property of `n = 8`.** At `n = 11` the
same enumeration over speeds `≤ 26` (973 196 candidate sets past the ladder filter)
returns **exactly one** tight instance, the AP `{1,…,10}` — which is precisely what
v33's hyperplane exclusion removes. `[EMPIRICAL — exhaustive over speeds ≤ 26]`
The exposure is `n = 8`-specific and is created by the two extra tight instances.

## 5. And it breaks sign-range containment  `[PROVED, as to the naive global form]`

v33 Lemma 5.1 (`:371-372`) gives `a_j ∈ (j-1, j+1)` for `j = 2,…,9` in every
completely blocking configuration, and it is what reduces the problem to `2^8` sign
classes (`:400-401`). The naive `n = 8` analogue `a_j ∈ (j-1, j+1)`, `j = 2,…,6`,
**fails on both non-AP tight instances**:

| | `a_2` | `a_3` | `a_4` | `a_5` | `a_6` |
|---|---|---|---|---|---|
| `{1,2,3,4,5,7,12}` | `7/6` ✓ | `7/4` ✗ | `7/3` ✗ | `35/12` ✗ | `49/12` ✗ |
| `{1,4,5,6,7,11,13}` | `28/13` ✓ | `35/13` ✓ | `42/13` ✓ | `49/13` ✗ | `77/13` ✓ |

Both are large-ratio configurations (`a_1 < 1`), where `W_ref` holds ten or eleven
slots rather than six, so the global index `j ↔ j` is not the right pairing there.
**Stated as a flag, not as a refutation of Lemma 5.1**: if the intended form is
per-cycle rather than global, the `n = 8` translation needs that form written down
before any sign-class decomposition is attempted.

## 6. Where this leaves the route

The two results combine into a decomposition rather than a wall:

1. `T` outside the residual case → `t = 1/q` or `t = 1/8`. **One line, PROVED, and
   this is where every tight instance lives.**
2. `T` residual (multiples of 5, 6, 7 and 8) → tightness is not in evidence here
   (`min M = 2/15` over speeds `≤ 32`), so the good set has nonempty interior and a
   **measure** argument — the v33 architecture's actual target — is available.

That is the repair: the v33 architecture applies exactly to the residual case, and
the instances that break it are exactly the ones the ladder already settles. What is
owed before this can be leaned on: whether `inf{M(T) : T residual} > 1/8` at all, which
is open and is the sharp question this file hands forward.

## 7. Ledger

Nothing here proves `n = 8`. Established: the extremal boundary at `n = 8` is three
sets up to 24, all tight for the `q = 8` reason; the Lebesgue-`GF` target of the
`n = 11` method is false at `n = 8` with two explicit off-hyperplane witnesses; the
naive sign-range box fails on the same two; `n = 11` has one tight instance up to 26
and is therefore not exposed the same way.
**Owed:** the `≤ 34` sweep, the residual-case `min M` run, and whether the residual
infimum exceeds `1/8`.
