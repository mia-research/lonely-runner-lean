# The moment lies in the first neighbour interval (v2)

2026-09-13. n = 8, individual isolation, threshold 1/8, arbitrary distinct sorted speeds.

**Changes in v2**, both from `SKETCH_DEBTS_v2` §4:
(i) **C1** — §1 step 3 said "verify the other **five**"; it is **six**. `d_min` comes from the
nearer neighbour, so the second neighbour is read like everyone else. Raised at handover
2026-09-13 §7 item 1.
(ii) **C3** — §5 restated "the good set always meets the first neighbour interval" and "the six
other constraints conspire to cover a stretch", which are register items 8 and 4. Restated in this
framework's own terms. §2 and §4 carried the same two words and are restated with them, since
fixing one occurrence and leaving three would make the file incoherent. No claim changes.

Nothing else is altered, and no grade moves.

Supersedes the framing of `MOMENT_ITERATION_v1` — which described a bounded iteration, correctly
but more elaborately than needed. The procedure below is the owner's and is simpler.

---

## 1. The procedure

To find when runner `i` is first lonely:

1. **From its two neighbours**, `d_min = min(v_i − v_{i−1}, v_{i+1} − v_i)`. Exact — speeds are
   sorted, so the nearest speed *is* a neighbour.
2. **That fixes one interval**, `[ 1/(8·d_min), 7/(8·d_min) ]` — the first stretch on which the
   nearest neighbour is clear of the threshold.
3. **Verify the other six inside it.** The first point where all clear is the moment.

To predict r2 you need r1 and r3, and then you check the rest against the times that interval
throws up. Nothing more.

**Six, not five.** `d_min` is supplied by the *nearer* of the two neighbours; the second neighbour
is then read exactly like every other runner and must be verified with them. Six others remain, not
five. Dropping the second neighbour changes the answer: at `V = (4, 12, 29, 37, 101, 121, 176, 196)`
runner r4, checking five returns `1/8` while the full reading gives `9/64`; the two differ in 3,276
of 48,000 runner-instances.

## 2. The moment is always in the FIRST interval  `[VERIFIED — 21,600 of 21,600]`

Containment in *some* neighbour interval is forced — wherever runner `i` is clear of everyone, it
is in particular clear of its nearest neighbour. That the moment lies in the **first** such
interval is not forced, and is the measured claim: a runner's first clear point could in principle
fall in the second interval or later. It never did.

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

**Confirmed independently, 2026-09-15.** Two further runs, differently posed, agree: 12,000
runner-instances at five spans reporting the *lap index* of first clearance returned lap 0 in every
case, and 12,800 on an independent seed, asked as "clear in the first window" against "clear
anywhere in a full period", found no runner clear somewhere but not in the first window. Combined
with this section's 21,600, the claim stands at 46,400 with no exception, and it remains
`[VERIFIED]` — none of these runs is a proof.

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
leaves `3/4` of it clear, so a naive independence estimate leaves about `(3/4)⁶ ≈ 0.18`
of it — comfortably nonempty. That is a heuristic for why the interval is rarely exhausted, **not**
a proof that a clear point always lies inside it. The 21,600 cases are the evidence.

## 5. Status and scope

`[PROVED — arithmetic]` step 1 (locality of `d_min`) and containment in *some* neighbour interval.
`[VERIFIED — 21,600 of 21,600]` §2, the first-interval claim, across seven populations including
adversarial ones.
`[SUPERSEDES]` the step-count framing of `MOMENT_ITERATION_v1`; the "no closed form" framing of
`GENERAL_MOMENT_RULE_v1` §5 and `RANDOM_PREDICTION_v1` §5.

**Scope.** n = 8 throughout. Populations as tabulated; irrational speeds untested here, though the
arithmetic is identical.

**Not established.** A proof that runner `i` always comes clear somewhere inside its first
neighbour interval. §4 is a density heuristic, and a counterexample would need the six other
readings to leave no clear point anywhere in a stretch of length `3/(4·d_min)` — not obviously
impossible.

**n = 8 is not proved here, and is not the target here.**
