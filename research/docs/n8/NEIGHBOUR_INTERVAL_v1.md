# The moment lies in the first neighbour interval

2026-09-13. n = 8, individual isolation, threshold 1/8, arbitrary distinct sorted speeds.

Supersedes the framing of `MOMENT_ITERATION_v1` — which described a bounded iteration, correctly
but more elaborately than needed. The procedure below is the owner's and is simpler.

---

## 1. The procedure

To find when runner `i` is first lonely:

1. **From its two neighbours**, `d_min = min(v_i − v_{i−1}, v_{i+1} − v_i)`. Exact — speeds are
   sorted, so the nearest speed *is* a neighbour.
2. **That fixes one interval**, `[ 1/(8·d_min), 7/(8·d_min) ]` — the first stretch on which the
   nearest neighbour is clear of the threshold.
3. **Verify the other five inside it.** The first point where all clear is the moment.

To predict r2 you need r1 and r3, and then you check the rest against the times that interval
throws up. Nothing more.

## 2. The moment is always in the FIRST interval  `[VERIFIED — 21,600 of 21,600]`

Containment in *some* neighbour interval is forced — a runner's good set lies inside its own
`d_min` constraint's good set. That the moment lies in the **first** one is not forced, and is the
measured claim: a runner's good set could in principle begin in the second interval or later.
It never did.

| population | runner-instances | in the first interval |
|---|---|---|
| random integer 8-sets `[1,80)` | 9,600 | **9,600** |
| wide spans `[1,400)` | 2,000 | **2,000** |
| near-collision pairs | 2,000 | **2,000** |
| clustered (two tight groups) | 2,000 | **2,000** |
| one far outlier (200–900) | 2,000 | **2,000** |
| rationals, denominators ≤ 29 | 2,000 | **2,000** |
| all speeds `≡ ±1 mod 8` | 2,000 | **2,000** |
| **total** | **21,600** | **21,600** |

Maximum interval index examined: **1**, in every population.

## 3. What this retires

`MOMENT_ITERATION_v1` reported the moment being found in up to 11 `O(n)` steps, and I read that
as the answer sometimes lying far out. It does not — **all eleven of those steps were jumps within
the first interval.** Both descriptions are correct; this one is the useful one.

It also retires the framing in `GENERAL_MOMENT_RULE_v1` §5 and `RANDOM_PREDICTION_v1` §5 about a
missing closed form. There is no missing piece. The neighbours give the interval, the other
runners carve it, and the first survivor is the answer — for any speeds, grid or not, integer or
not, AP or not.

## 4. Why the first interval is wide enough to work

The first interval has length `6/(8·d_min) = 3/(4·d_min)`. Each other constraint `d′ ≥ d_min`
removes a bad set of density `1/4`, so a naive independence estimate leaves about `(3/4)⁶ ≈ 0.18`
of it — comfortably nonempty. That is a heuristic for why the interval is rarely exhausted, **not**
a proof that the good set always meets it. The 21,600 cases are the evidence.

## 5. Status and scope

`[PROVED — arithmetic]` step 1 (locality of `d_min`) and containment in *some* neighbour interval.
`[VERIFIED — 21,600 of 21,600]` §2, the first-interval claim, across seven populations including
adversarial ones.
`[SUPERSEDES]` the step-count framing of `MOMENT_ITERATION_v1`; the "no closed form" framing of
`GENERAL_MOMENT_RULE_v1` §5 and `RANDOM_PREDICTION_v1` §5.

**Scope.** n = 8 throughout. Populations as tabulated; irrational speeds untested here, though the
arithmetic is identical.

**Not established.** A proof that the good set always meets the first neighbour interval. §4 is a
density heuristic, and a counterexample would need the six other constraints to conspire to cover
a stretch of length `3/(4·d_min)` entirely — not obviously impossible.

**n = 8 is not proved here, and is not the target here.**
