# The relay test, a profile-space search, and the `K ≤ 28` ceiling claim

---

## 1. Their relay claim — supported

*"High cascade depth requires all 7 disparities participating as multi-step setters."* Measured over
~12,000 subjects:

```
   depth    n      mean distinct setters
     1    6144            1.000
     2    3904            2.000
     3    1977            2.984
     5     372            4.441
     8      28            5.607   (max 6)

   23-move: 7 of 7      28-move: 7 of 7
```

Distinct setters track `min(depth, 7)` closely and saturate slowly — at depth 8 the mean is still
5.6 and the maximum 6. Both deep cases use all seven. **Their claim holds.**

## 2. Their two wall derivations — correct, verified

```
  wall 1:  D₁₈ = 175/41 (setter 175 at lap 5)  =  d₀/7  (d₀'s boundary at lap 1)
           ⟹ d₀ = 1225/41 = 29.878049
           measured: depth 18 just below, 23 just above          ✓ as they state

  wall 2:  D₁ = d₆/9 (setter d₆ at lap 1)  =  175/7 = 25  (175's boundary at lap 1)
           ⟹ d₆ = 225
           measured: 224.999 → depth 23,  225.001 → depth 1      ✓ as they state
```

Both match my bisections exactly, and the derivations correctly identify *which* step and *which*
lap produce each wall — more than my bisection gave. They have also dropped the divisibility
explanation ("requiring no appeal to integer divisibility or parity"), which resolves the point from
`CROSSCHECK_PARALLEL_v2` §3.

A third wall, from the depth-28 cell, fits the same form: its lower boundary is
`2002/41 = 286·7/41`, with `286` a disparity of that case, `7 = 8·1−1`, `41 = 8·5+1`.

## 3. Their `K ≤ 28` ceiling claim — **not established, and the evidence runs against it**

> *"For `K ≥ 29`, the simultaneous system of 29 linear half-spaces becomes over-constrained and
> empty, making `K = 28` the absolute geometric limit for 8 runners."*

**This does not follow.** Adding half-spaces contracts a cone; it does not empty it at any particular
`K`. Nothing in the argument singles out 29 over 28 or 40. An open polyhedral cone can be
arbitrarily thin and still nonempty — which is exactly what a decaying width law describes.

**And it is not a small claim.** `LRC/Spec/Target.lean` proves `existence_of_capped` and
`capped_of_existence` in both directions: a uniform bound on the cascade **is** Existence at order 8.
So `K ≤ 28`, if established, settles the open problem — and it cannot be established by observing
that constraints accumulate.

### 3.1 The measured evidence points the other way

The width law fitted over 96 cells, `log(width) = 3.710 − 0.1754·K`, decays **smoothly** and is
positive at every `K`:

```
   K = 23 → 0.723    K = 28 → 0.301    K = 29 → 0.252    K = 40 → 0.037
```

Nothing distinguishes 29. And the depth-28 cell is not degenerate — bisected on the `d_min` axis:

```
   [48.829268, 49.021277]   width 0.192008
```

An ordinary cell of positive width, the same order as the law predicts (0.30). **If 28 were a
geometric limit, the depth-28 cell should be collapsing to a point.** It is not.

### 3.2 What would be needed

A ceiling needs an argument that some specific finite intersection is empty — a linear-programming
infeasibility certificate for the word system at `K = 29`, or a bound on the achievable product of
dilations. Neither is offered. Until then the honest statement is: **no search has exceeded 28**,
which is what my four seeded climbs, three construction routes and their perturbations all say, and
which is a statement about searches.

## 4. My own profile-space search — no better

Searching directly in reading space (6 continuous parameters, 300 restarts, instantiated at
`c = 2000`) rather than integer space:

```
   1 profile with depth ≥ 22;  best depth 23
   [1.000, 4.009, 4.612, 5.102, 5.707, 6.436, 7.270]
```

That profile is **family-B shaped** (one small reading, six clustered high) — found independently by
a different search in a different space, which corroborates the two-family picture. It did not beat
28 either.

```bash
python3 experiments/n8/relay_v1.py         # distinct setters vs depth; profile-space search
python3 experiments/n8/ceiling_test_v1.py  # wall verifications; the width trend through K=28
```
