# Audit: which numbers were left as statistics?

**Owner, 2026-09-18:** *"it begs the question what else have you treated as statistic and not
followed it to its logical conclusion."*

Every quantity in this project is a deterministic arithmetic fact about a finite object. A
percentage is therefore never the end of an investigation — it is a partition waiting to be named.
Here is the audit of this session's numbers.

---

## 1. Closed — the number has a criterion

| figure | criterion | status |
|---|---|---|
| 81.3% of colliding blocks exact | `r = 0`, i.e. `c ∣ b(8N+1)` | 5305/5305 |
| non-colliding never exact (0/12,152) | `8 ∣ a(8N+1)`, `8N+1` odd ⟹ `8 ∣ a` | `[PROVED]` |
| smallest near-block host `c = 9` | `r ∈ [1,c−1]` + near ⟹ `c > 8` | `[PROVED]` |
| near blocks split 731:260 | readings grow monotonically ⟹ caught on entry | 6278/6278 |
| cascade margin always `1/8` | final move sets `t = (k+1/8)/d` | 4000/4000 |
| 49.7% unique residue | `spine_all_or_nothing` | `[PROVED]` |
| 12,800/12,800 `±p` rule | `(Δ·p) ≡ 1`, `p⁻¹ = p` in Klein | `[PROVED]` |
| 16,000/16,000 laps invisible | `gridPos_congr` | `[PROVED]` |
| 76.5% union bound | closes iff ≤ 3 disparities uncaged | quantised at `k/4` |

## 2. Closed **this session by the audit** — previously left as percentages

### 2.1 "63.8% / 53.5% clear at `d_min` with zero cascade moves"

Reported repeatedly with no criterion, and I refuted a parallel session's theorem for exactly this
case without supplying the right one. The criterion, in reduced units with `c = d_min/g`:

> **clear at `d_min` ⟺ every disparity satisfies `c ≤ a mod 8c ≤ 7c`**

`DminClearance.clear_iff`, axiom-clean, plus `bad_iff`. Verified **32,000 / 32,000** against the
cascade (`dmin_criterion_v1.py`). The "unique residue" predicate agrees only 57.2%.

### 2.2 And it says exactly when the parallel session's theorem *is* right

Set `c = 1`. The criterion becomes `1 ≤ a mod 8 ≤ 7`, i.e. `a mod 8 ≠ 0` — **which is literally
"unique residue"**. So:

> their proposed `Iff` is the `d_min = g` special case, and correct there.

Measured 2449/2449 agreement whenever `c = 1`, and this is an algebraic identity, not a sample.
That is a more useful statement than "false in both directions" (which it also is, in general) and
it supersedes the flat refutation in `FILTER_ASSESSMENT_AND_CROSSCHECK_v1` B.3.

---

## 3. Still open — named, not hidden

These are deterministic and I have not followed them:

| figure | what is missing | assessment |
|---|---|---|
| **10.4%** cascade neighbour residue-determined (null 1.9%) | *which* subjects? | most likely to close — the cascade is a function of `ds`, and `ds` fixes `\|offset\|` but not offset, so the 10.4% should be characterisable by where the sign is recoverable |
| **0.4017 / 0.4148** depth agreement vs floor 0.3758 | any criterion for depth at all | hardest. Depth is not determined by `π` or `q` separately; a criterion would have to be joint |
| **0.3409 / 0.3540 / 0.6789** binding neighbour is the speed-neighbour | criterion | tractable: at a grid instant it asks when the rank-adjacent runner has offset `±p` |
| **1.93×** colliding setter ratio | closed form for the constant | partly explained (§6 of `COLLIDING_MECHANISM_v1`); the exact value probably has none |
| **M unbounded** (found 20) | growth characterisation | open; the margin hypothesis is already dead |
| 0.1800 / 0.0025 invariance for general arrangements | criterion | the grid column is `1.0000` and proved; the general column is not characterised |

### 3.1 A criterion I proposed and the data refuted, in the same run

I guessed that the multiplier and cascade witness denominators tie (10.0%) exactly when the subject
clears at `d_min` **and** `M = 1` — both routes stopping at the first instant. **False**: of 240
ties, 229 have depth 0 but 11 have depth 2–6 (`audit_leftovers_v1.py`). Recorded as a refuted guess
rather than deleted, since the failure is the datum: a tie does not require either route to be
trivial.

---

## 4. The methodological point

The pattern in §1 and §2 is that **every one of these closed to a short arithmetic statement**, and
several to one-line proofs. The 81.3% became `r = 0`; the 0-of-12,152 became "`8N+1` is odd"; the
63.8% became a residue band. None needed new machinery.

So the working rule this audit earns:

> **A percentage over a deterministic finite population is an unfinished partition.** Before
> reporting one, ask what distinguishes the two sides — and if the answer is arithmetic, it is a
> theorem, not a rate.

That sits alongside the two guards already recorded: compute the forced floor before interpreting
an agreement rate, and control the confound before believing a signal.

```bash
cd LonelyRunner && lake env lean ../experiments/n8/DminClearance_v1.lean
python3 experiments/n8/dmin_criterion_v1.py     # 32,000/32,000
python3 experiments/n8/audit_leftovers_v1.py    # the c=1 identity; the refuted tie guess
```
