# C1 — the construction, with the base determined

2026-09-15. Replaces `C1_MIXED_CONSTRUCTION_v1`, whose base family was the four eighths only and
which left 2.5% open. The base is now **determined rather than searched**, and nothing has failed.
**This is still not a proof.**

---

## 1. The construction

For subject `i`, reading `s_1 = 1, …, s_7`:

**Base.** Either one of the four reference instants `u = p/8`, `p` a unit mod `n`; or an instant
at which the **farthest** runner is diametrically opposite the subject —

    u  =  (2k+1) / (2·s_max)        the phase of s_max there is exactly 1/2

**Move.** From the base, in one direction, to the earliest instant at which every blocked runner
has cleared. A runner is *clear* at the base when its phase lies in `[1/8, 7/8]` and *blocked*
otherwise; moving by `ε`,

| | moving right | moving left |
|---|---|---|
| clear `j` stays clear while | `s_j ε ≤ 7/8 − phase` | `s_j ε ≤ phase − 1/8` |
| blocked low (`phase < 1/8`) needs | `s_j ε ≥ 1/8 − phase` | `s_j ε ≥ phase + 1/8` |
| blocked high (`phase > 7/8`) needs | `s_j ε ≥ 1 − phase + 1/8` | `s_j ε ≥ phase − 7/8` |

Take `ε` = the largest requirement over the blocked; it is admissible when it fits inside the
smallest room over the clear.

## 2. Why the base is an end runner  `[PROVED]`

`s_max = d_max/d_min`, and `d_max = max_j |v_i − v_j|` is attained at `j = 1` or `j = 8` because
the speeds are sorted. So:

> **The runner whose opposition instants supply the base is always an end runner — and for the
> end subjects it is the other end, the wrap partner.**

Measured: interior never, 0 of all; r1's farthest is r8 in 1,481/1,481; r8's farthest is r1 in
1,546/1,546.

**The ends are not the subjects with the difficulty.** Spine failures are spread evenly over the
subjects and are *lowest* at the ends — r1 33, r2 73, r3 71, r4 57, r5 69, r6 69, r7 89, r8 49.
The ends are where the resolution comes from, for every subject.

## 3. Verification  `[VERIFIED — 162,694 runner-instances, 0 failures]`

Every instant returned was re-checked to be a genuine isolation instant lying in `[1/8, 7/8]`.
Only runners needing more than the ratio condition `d_max ≤ 7·d_min` are counted.

| population | runners | failures |
|---|---|---|
| random `[0,120)` | 2,802 | 0 |
| random `[0,20000)` | 2,830 | 0 |
| near-collision | 2,967 | 0 |
| clustered (two tight groups) | 4,000 | 0 |
| one far outlier | 3,500 | 0 |
| **exhaustive integer arrangements to span 22** | **146,595** | **0** |
| **total** | **162,694** | **0** |

The base narrowing is what changed: spine only settles 96.6%; spine plus the farthest runner's
opposition instants settles everything measured. Searching *all* runners' opposition instants is
not needed, and a `k`-capped version is not enough — `k ≤ 5` over every runner leaves 0.28%.

## 4. What this is, and is not

**Sound** — every instant it returns is an isolation instant in the window, checked, without
exception. **Not complete, as a theorem.** Two things are verified rather than proved:

- that the largest blocked requirement fits inside the smallest clear room at some base in the
  family — checked per case;
- that the index `k` needed is finite — the enumeration terminates in practice, and no bound is
  proved.

So this has exactly the epistemic standing of the owner's own first-interval claim: a procedure
with no observed failure over a large and adversarial sample. It is evidence about C1, not a
proof of it.

**What would close it.** A condition on the reading guaranteeing the fit at a named base — the
way `s_j ≤ S(7−c_j)` does for the integral blocked case in `C1_INTEGER_CONSTRUCTION_v1` §2 —
together with a bound on `k`. The `s_max` narrowing is what makes that plausible to state: the
base is no longer "some runner's opposition instant" but "the end runner's", and at that instant
the farthest runner has maximal clearance, `1/2`, which is the largest room available anywhere.

## 5. Status

`[PROVED]` §1's inequalities; §2's identification of the base runner as an end runner.
`[VERIFIED — 162,694, 0 failures]` §3.
**`[OPEN]` C1.**

**n = 8 is not proved. C1 is not proved.** What changed across this session is the shape of what
is left: from an unstructured 68.6% open, to a single named procedure whose only unproved parts
are one inequality's feasibility and one index's finiteness.
