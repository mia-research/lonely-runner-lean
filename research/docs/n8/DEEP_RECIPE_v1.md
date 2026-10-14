# Can we construct deep examples? Yes — at known depths, at any scale

**Answer: yes for reproducing, no for exceeding.**

---

## 1. The recipe

Pick any minimum `c`. Set `d_i = round(c · r_i)` for one of the two profiles:

```
  PROFILE A   r = [1, 74/30, 96/30, 127/30, 159/30, 175/30, 224/30]
              ≈ [1, 2.4667, 3.2000, 4.2333, 5.3000, 5.8333, 7.4667]

  PROFILE B   r = [1, 205/49, 234/49, 256/49, 286/49, 323/49, 366/49]
              ≈ [1, 4.1837, 4.7755, 5.2245, 5.8367, 6.5918, 7.4694]
```

Measured over `c = 20 … 400` (381 transplants each):

```
  PROFILE A   mean depth 22.56   median 23   P(≥20) = 0.992   P(=23) = 0.682
  PROFILE B   mean depth 19.76   median 28   P(≥25) = 0.564   P(=28) = 0.549
```

Worked examples at a fresh scale:

```
  c = 400, profile A:  [400, 987, 1280, 1693, 2120, 2333, 2987]        depth 23
  c = 400, profile B:  [400, 1673, 1910, 2090, 2335, 2637, 2988]       depth 28
  c = 3000, profile B: [3000, 12551, 14327, 15673, 17510, 19776, 22408] depth 28
```

**So deep cases are now constructible on demand rather than only findable by search.** That is the
practical gain: arbitrarily large deep instances for stress-testing, at any lattice size.

## 2. What it does not do — three independent attempts to exceed, all negative

| attempt | result |
|---|---|
| transplant the profile to 381 new scales | reproduces its own depth, **never exceeds** it |
| hill-climb seeded at the record, scales ×1/×4/×12/×40, 60k steps each | never exceeds 28 |
| interpolate between the two families in reading space | a **valley** — depth falls to 5–12 |

The interpolation is the informative one:

```
   u:    0.00  0.05  0.10  0.25  0.50  0.75  0.90  0.95  1.00
  depth:   23    12     7     8     7     8     5     5    28
```

**The two deep profiles are isolated peaks, not ends of a connected deep region.** So constructing
something deeper needs a *new* profile, and nothing here supplies a method for finding one — the
three routes that would have (refine, climb, interpolate) are all closed.

## 3. Why the recipe works, in terms already established

A profile is a point in the projectivised disparity space, and depth is constant on the cones cut by
the walls `q·a_i = p·a_j`. Transplanting a profile to a new `c` lands in **the same cone**, up to
rounding — so the depth is the same. The failures are exactly the roundings that fall across a wall,
which is why `P(=23) = 0.682` rather than 1, and why the success rate rises with `c` (the best
transplants are all at `c ≈ 400`).

That also explains the interpolation valley: the straight line between two cones passes through many
others, and nothing makes the intermediate cones deep.

## 4. Grade

`[EMPIRICAL]` throughout. Every individual instance is exact — depths computed in `Fraction`
arithmetic and re-verified — but the success rates are over `c = 20…400` with these two profiles,
and "never exceeds" is a statement about three specific searches, not a bound. My searches have been
beaten before in this session (`M ≤ 7` became 20 under a harder climb).

```bash
python3 experiments/n8/transplant_v1.py   # the recipe, 381 transplants per profile
python3 experiments/n8/blend_v1.py        # the interpolation valley
```
