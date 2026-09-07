# PREREG — the RIGID class of speed tuples (C1 & C2 sweep), v1

**Status: PRE-REGISTRATION, written before any rigidity datum is seen. Not a result.** 2026-09-07.
Every number the run emits inherits §6. **Provenance of numbers already here:** only *frame*
combinatorics and *timing* were computed to fill §5 (how many tuples satisfy C1/C2; cost of
`lonely_set`). Neither touches `RIGID`. Pilot seed **20260907**, deliberately distinct from §3's run seed.

## 1. Object, and the tautology check
`L(T,n) = { t in [0,1) : ||v t|| >= 1/n for all v in T }`, `T` a set of `n-1` distinct positive
integers. `T` is **RIGID** iff `L(T,n)` is exactly `{ r/n : 1 <= r < n, gcd(r,n)=1 }`: all `phi(n)`
points present, no other isolated point, no positive-length component. Computed by `lonely_set(T,n)`
in `experiments/n8/exact_phi_n_ap_v1.py` (Boundary Set Method, event-complete).
**C1**: `{v mod n : v in T}` contains every unit of `Z/nZ`. **C2**: for every `q` in `2..n-1` some
`v in T` is divisible by `q`.

Not a tautology: C1/C2 are read off `T` by residue and divisibility, `RIGID` off the exact real set
`L(T,n)` — disjoint construction, one shared input. **But** the owner reports a proof of NECESSITY
for each of C1 and C2. If those proofs hold, the `notC1` and `notC2` cells are *analytically forced*
and carry **zero information about the hypothesis**; they test the proofs and the pipeline only. All
hypothesis-bearing content sits in the sufficiency cell. Recorded now so a forced count is never
later reported as confirmation.

## 2. Statistic and decision rule (one primary statistic)
**`K` = number of frame tuples satisfying `C1 and C2` that are not RIGID**, per `n`, reported with
the explicit list of every such tuple — the falsifiers are the artefact, not a rate.
Joint sufficiency is **FALSIFIED at `n`** iff `K >= 1`. Necessity of C1 is **FALSIFIED** iff some
RIGID tuple has `not C1` (`M1 >= 1`); C2 likewise (`M2`).

Null distribution: exhaustive arms (§3) have none — `K` is the exact count over the whole frame and
the only residual uncertainty is scope. Sampled arms: under failure rate `eps`, `K ~ Binomial(N_both, eps)`.
Report the full 2x2 per `n` — `(C1&C2)` x `RIGID` — all four cells, with counts and arm sizes.

**Mandatory structure log; a bare binary is an incomplete run.** For every `C1&C2` tuple that is not
RIGID, and every near-miss tuple that *is* RIGID: which `r/n` are missing, which extra isolated points
appear (exact Fractions), every positive-length component as an exact endpoint pair, the failing `q`
and the uncovered unit. Plus, across the whole near-miss arm, the distribution of *how many* of the
`phi(n)` points survive. This is what stops a `K=0` outcome collapsing to "nothing there" when the
effect may live in *which* points survive rather than whether.

## 3. Population, sampling, exhaustiveness
Frame: `T` an (n-1)-subset of `[1, 4n]` inclusive. (PART 4 of `exact_phi_n_ap_v1.py` used `[1, 4n-1]`
— a different frame; do not merge those counts.) Lexicographic enumeration is banned as a *sample*;
permitted only where the arm is exhaustive, and even then the reported listing must be shuffled so
no output is lexicographically truncated.

| n | population C(4n,n-1) | arm | note |
|---|---|---|---|
| 4 | 560 | exhaustive | |
| 5 | 4 845 | exhaustive | |
| 6 | 42 504 | exhaustive | |
| 7 | 376 740 | exhaustive | ~17 min, 1 core |
| 8 | 3 365 856 | exhaustive | ~3.6 h, 1 core; chunk by first element if parallelised |
| 9 | 30 260 340 | sampled | |
| 10 | 273 438 880 | sampled | |
| 11 | 2 481 256 778 | sampled | |
| 12 | 22 595 200 368 | sampled | |

For `n <= 8`, "no counterexample" is **exhaustive** over `max(T) <= 4n`, not a rate. Sampled arms, seed `8081729 + 1000*n + arm_index`:
- **Arm 0, uniform stratum** (`n=9,10`): uniform (n-1)-subsets of `[1,4n]`, kept iff C1&C2, to 20 000.
  Unbiased on the stratum, so Arm 0 rates are population rates.
- **Arm 1, constructive** (`n=11,12`, where naive acceptance is 0.009% / 1.3%): pick a uniform unused
  multiple of each `q` in `2..n-1`; then a uniform unused `x = u (mod n)` for each uncovered unit `u`;
  fill remaining slots uniformly; restart if size exceeds `n-1`. Target 20 000. **Biased on the
  stratum. Pre-commitment: Arm 1 reports counts and arm size only — no rate, no density, no "fraction
  of C1&C2 tuples that are rigid" may be computed from it.**
- **Arm 2, matched near-miss control** (all sampled `n`): uniform subsets kept iff exactly one of C1,
  C2 holds; 20 000 per `n`, split by which one fails.
Sample fractions of the C1&C2 stratum at 20 000: n=9 ~12%, n=10 ~0.34%, n=11 ~9%, n=12 ~0.007%.

## 4. Matched control, and the controls that must fire
**Matched control = Arm 2.** Matched on `n`, tuple size, range `[1,4n]`, draw procedure; differs only
in satisfying exactly one of C1, C2. It preserves every structure the C1&C2 arm has except the
conjunction. No shuffle control is used and none would be valid: permuting `T` destroys divisibility
and residue structure, i.e. destroys C1 and C2 themselves — the null-mismatch pattern this project has
already been burned by. **Discriminancy: if Arm 2's RIGID count is not 0 the contingency does not
separate, and that same event is a necessity falsification by §2. One event, reported once.**

**Firing controls, both directions, run first, abort on failure.**
1. *Not-rigid*: `T = {1,3,5,7,9,11,13}`, `n=8`. Must print `C1=True`, `C2=False (q=2)`,
   `RIGID=False`, `len(ivs) >= 1`, every interval as an exact endpoint pair, and at least one interval
   containing `1/2`. **Pass criterion: `RIGID=False` with an interval containing `1/2`.** The owner
   states five components; the run prints the count, and a count other than 5 is a *disclosed
   discrepancy against the owner's figure* — not silently absorbed, and not a pipeline failure.
2. *Rigid*: `{1,...,7}` at `n=8`; `{1,2,3,4,5,7,12}` at `n=8`; `{1,3,4,7}` at `n=5`. Each
   must print `RIGID=True`, exactly `phi(n)` isolated points, zero intervals. Without this arm a test
   stuck on "not rigid" passes control 1.

**Planted controls (forced effect of known size; must fire 100%).** (a) 20 all-odd tuples per `n` in
4..12: `||v/2|| = 1/2 >= 1/n` for odd `v`, so a component containing `1/2` is forced — the run must
flag **20/20** not-RIGID with that interval. (b) 20 tuples per `n` satisfying C2 but omitting a chosen
unit residue `u`: each must report a missing or non-isolated `r/n`. **If either plant does not fire at
100%, the sweep is void and no `K` may be reported.**

## 5. Power (computed now, from the pilot — not after)
C1&C2 rates in the frame; exhaustive for `n<=7`, Monte Carlo (200 000 draws, pilot seed) above.

| n | rate(C1&C2) | expected C1&C2 tuples in arm | rate(C1 xor C2) |
|---|---|---|---|
| 4 | 0.164286 = 92/560 exact | 92 | 0.610 |
| 5 | 0.027451 = 133/4845 exact | 133 | 0.552 |
| 6 | 0.121118 = 5148/42504 exact | 5 148 | 0.575 |
| 7 | 0.004542 = 1711/376740 exact | 1 711 | 0.396 |
| 8 | 0.02212 MC | ~74 450 | 0.393 |
| 9 | 0.00541 MC | 20 000 capped | 0.325 |
| 10 | 0.02150 MC | 20 000 capped | 0.344 |
| 11 | 0.00009 MC | 20 000 capped (Arm 1) | 0.213 |
| 12 | 0.01310 MC | 20 000 capped (Arm 1) | 0.291 |

The sufficiency cell is **not** near-empty at any `n`: the smallest are 92 (`n=4`), 133 (`n=5`) and
1 711 (`n=7`), all in exhaustive arms. The test can come out either way — the failure mode guarded against.
- Exhaustive arms (`n<=8`): power **1** against any counterexample with `max(T) <= 4n`; **zero** power outside it.
- Sampled arms, `N_both = 20 000`: `P(K>=1) = 1-(1-eps)^20000` — **95%** at `eps >= 1.50e-4`, **99%** at
  `2.30e-4`, **50%** at `3.47e-5`. Below `eps ~ 1e-5` they have essentially no power; that sentence must
  accompany every sampled-arm null. Necessity (`M1`,`M2`): decided with certainty for `n<=8` in-frame,
  same power curve for `n>=9`. Measured cost: `lonely_set` 0.55 ms (n=4) to 13.1 ms (n=12) per tuple.

## 6. SCOPE (attaches to every number)
`T` a set of `n-1` distinct positive integers, `max(T) <= 4n`; `n` in `4..12`; bound `1/n`; exact
rational arithmetic; `lonely_set` from `experiments/n8/exact_phi_n_ap_v1.py` at the SHA-256 the run
records. Exhaustive `n in 4..8`; sampled `n in 9..12` at the stated arm sizes. No claim extends to
`max(T) > 4n`, `n > 12`, multisets, non-integer or negative speeds, or bounds other than `1/n`.

## 7. Falsification, written before the run
Joint sufficiency abandoned on **one** C1&C2 tuple that is not RIGID. Necessity of C1 (resp. C2)
abandoned on one RIGID tuple with `not C1` (resp. `not C2`) — that event also refutes the §1 analytic
proof, and the proof, not the sweep, is what was wrong. The sweep is void if either §4 plant misfires,
either firing control misreports, or §8 finds a float breach on the signal path.

## 8. Exactness
**No float may be constructed on the signal path.** Times, crossings, midpoints, norms are
`fractions.Fraction`; residue and divisibility work is `int`. No tolerance, no `abs(x-y)<eps`, no
`float()`, no `math.*`. **Carve-out: none** on the signal path; floats permitted only in wall-clock
timing and progress printing, which no branch may read. Detection: (a) run
`experiments/n8/float_audit_v1.py` (AST audit: true division, float literals, `float`/`round`,
`math.*`) over the sweep script *and* `exact_phi_n_ap_v1.py`, recording output verbatim; (b) an
inner-loop assertion that every `t`, cut and norm is `isinstance(x, Fraction)`; (c) record and assert
the SHA-256 of `exact_phi_n_ap_v1.py` — this is what enforces "reuse, do not rewrite". Pinned breakage
risk: that module has **no `if __name__ == "__main__"` guard**, so importing it executes PARTS 1-4 and
prints; the sweep must import `lonely_set`/`norm` with output suppressed and must not edit the module.

## 9. Pre-committed conclusions (fixed now, one per outcome)
| outcome | conclusion, fixed in advance |
|---|---|
| `K=0` for all `n` | **C1 & C2 jointly sufficient — EMPIRICAL, scope §6.** Fixed wording: "no C1&C2 tuple with `max(T) <= 4n` fails rigidity for `n <= 8` (exhaustive); `n = 9..12` sampled at 20 000, 95% power only above failure rate 1.5e-4." A proof of sufficiency becomes the next target. Grade stays EMPIRICAL. |
| `K >= 1` at some `n` | **Joint sufficiency is false.** The finding is the falsifier list plus its §2 structure log — whether the failures share a residue class or a `q`. The next object is the third condition they isolate. This is a **positive** outcome and must not be written as "the rigid class is not characterisable". |
| `M1 >= 1` or `M2 >= 1` | A §1 necessity proof is wrong. Report the RIGID tuple, quote the step it breaks, retract the condition. Do not repair the condition and re-test on the same data. |
| Arm 2 RIGID count > 0 | Same event as the row above (§4). Report once, as a necessity falsification, noting that the contingency does not separate. |
| `n<=8` clean, sampled `n>=9` yields `K>=1` | The condition is `n`-dependent. Report the smallest breaking `n`; the exhaustive small-`n` result keeps its scope and is not retracted. |
| Any arm not run | **ABSTAIN on that arm, in the grade slot.** Abstention is **not** a closure of the rigid-class question and is not evidence either way. Record the arm as owed, with the reason. |
| `K=0` everywhere | Explicitly **not** licence to write "C1 & C2 characterise RIGID". `K=0` on a bounded frame is a bound with a stated power, not a theorem, and the necessity cells are forced (§1) so they add nothing. Still open after a clean run: a rigid tuple with `max(T) > 4n`, or at `n > 12`. |
