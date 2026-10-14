# Plan — an analytic proof of `n = 8`

2026-09-07. Written after reading `ROSENFELD_REVIEW_v1`, `HANDOVER_2026_09_07b`,
`SEARCH_REDUCTION_v5`, `WHY_13_AND_19_v2`, `CLAIM_GRADES_v1` and
`project_n8_rosenfeld_2026_09_07`. Supersedes nothing; there was no prior plan.

## 0. Process correction

Today's session produced four results — a `p`-uniform cap table, a top-gap theorem, a
refutation of `f(8,p) ≥ 6`, and a `U_min(2)` closed form — **without a plan**, each chosen
because it was the next cheap thing. Three consequences, recorded so they are not repeated:

- **The top-gap Lemma 2 is not a new idea; it is the corpus's own named target.**
  `WHY_13_AND_19_v2.md` §6 already states it: *"a uniform lower bound on the widest lonely
  interval over all admissible `k`-tuples — a quantitative strengthening of LRC ('a lonely
  time exists with room around it')."* Today's Lemma 2 is a first instance of exactly that,
  and it was framed as something else because §6 had not been read.
- **The `f(8,p)` work sits on an already-mapped relation.** `HANDOVER_2026_09_07b` §6.3
  records `f(n,p) ≤ n−3 ⟹ Lemma 7 fails at (n−1,p)`, one-way, converse false. The three
  new counterexamples `f(8,p) ≤ 5` at `p = 11,17,19` are instances of that implication.
- **A background job was reported "still running" five times on a check that could not tell
  running from hung.** The parent had 2.3 s of CPU in 59 minutes and zero workers. That is
  a proxy-for-object error, the failure mode this project's own agent rules name.

## 1. Two targets that must not be conflated

| | statement | strength | status |
|---|---|---|---|
| **(A)** | Lemma 6 holds for all `k`, all large `p` | **equivalent in difficulty to LRC** (`project_n8_rosenfeld` §5: proved implication, checked at `p = 101, 1009`) | not a shortcut; the author's own suggestion, and it is the conjecture restated |
| **(B)** | Lemma 6 at the **27 fixed primes** `S = {31,…,163}`, 41 absent | finite; **not** equivalent to LRC | **this is the target** |

Anything that proves (A) proves LRC. So "analytically prove `n = 8`" means **(B)**: replace
the 27-prime search by argument. The margin forbids dropping any prime —
`lcm({2..8} ∪ S) ≈ 1.82×10⁵⁵` against Corollary 3's `7.4×10⁵⁴`, a factor of only 2.49.

## 2. Dependency graph, with grades

1. **Theorem 2** (Malikiosis–Santos–Schymura, *Forum Math. Sigma* 13 (2025) e164) —
   `[CITED, peer-reviewed, proof not read]`. **Load-bearing for the entire argument.**
2. **Corollary 3** (AM–GM on Thm 2): a counterexample has `∏vᵢ < 7.4×10⁵⁴`. Elementary.
3. **Lemma 4**: `lcm(2,…,k+1) | ∏vᵢ` for any non-LR set. Elementary.
4. **Lemma 5**: needs LRC for `k−1` = `intLRC 7` — **we own it, machine-verified,
   axiom-clean**.
5. **Lemma 6/7**: the engine. The 27-prime search. **This is the only computational step.**
6. Contradiction by size.

**Gate, before anything is graded above CITED: `citation-verifier` on Theorem 2.**
`ROSENFELD_REVIEW_v1` §6 already flags this and it has not been run. It is mandatory under
`CLAUDE.md` §2 and it is the single largest unexamined dependency. Note the recorded trap:
MSS state the hypothesis in the **runners** convention and Rosenfeld transcribed it into a
**speeds** paper; do not transcribe his Theorem 2 verbatim.

## 3. The mechanism, and the exact arithmetic of why it is hard

`WHY_13_AND_19_v2` §1: Lemma 7 **fails** at `p` exactly when the grid `{j/N}`, `N = 8p`,
misses every lonely interval of some covering tuple. An interval of width `w` is guaranteed
hit once `Nw ≥ 1`, i.e. `p ≥ 1/(8w)`.

Speeds range over `{1,…,4p}`, so a tuple `T` with maximum `M` enters the search exactly when
`p ≥ M/4`. Writing `w(T)` for its widest lonely interval and

    ω(T) = w(T) · M(T)          (dimensionless),

`T` is safe at **every** `p` where it is in range iff `ω(T) ≥ 1/2`. So:

> **If `inf ω ≥ 1/2` over all LR-property 7-tuples, Lemma 7 holds for every `p`** — `n = 8`
> becomes computer-free, and by Rosenfeld §7 the same argument would attack all `k`.

**It is not `≥ 1/2`.** The known obstruction `T₇ = {1,4,12,13,14,16,20}` has `M = 20` and
widest window `1/384`, so `ω(T₇) = 5/96 ≈ 0.052` — short by a factor `9.6`. And what LRC(7)
currently proves (today's Lemma 2, six speeds) is `ω ≥ 1/28 ≈ 0.036` — short by `14`.

**This is the quantitative heart of the problem, and it is now stated in one number.** The
route is not vacuous: `ω(T) < 1/2` only makes `T` dangerous on the finite range
`p ∈ [M/4, 1/(8w))`, and `T₇` is dangerous on `[5, 48)` and actually fails at `41` alone.
So the real object is:

    for each p in S, the set of tuples with omega < 1/2 that are in range and missed.

## 4. Three routes, with what counts as progress and what falsifies each

**R1 — window width (the corpus's named target, `WHY_13_AND_19_v2` §6).**
Prove a uniform lower bound on `ω`. Progress = raising the proved constant from `1/28`
toward `1/2`, or proving a bound conditional on `M/p`. Falsified by exhibiting LR-property
tuples with `ω → 0` and `M ~ 4p`, which is the thing to measure first and has not been.
Nearest known machinery: Giri–Kravitz spectrum work, arXiv:2304.01462 **v4** (v3 withdrawn).

**R2 — finish `p = 163` (sectors `x = 3,2,1`).**
Named untried move (`HANDOVER_2026_09_07b` §6.1): invert the enumeration — the coarse side
is `C(81,x)`, small — and use the pair-type structure as a **branching rule**. Progress =
cells decided. **Ceiling: 5 of 135.** Does not generalise by itself, and must not be sold as
if it did.

**R3 — move quantities from per-prime to uniform-in-`p`.**
Today's cap table (`CAP_TABLE_UNIFORM_v1`) and `U_min(1), U_min(2)` (`P_UNIFORMITY_v1`) are
this. Progress = each per-prime input replaced by a formula. Measured dead end already
recorded: the `|D| ≥ U_min` filter never closes a sector, at any of the 27 primes, and the
gap widens.

## 5. The falsification test — cheap, implemented, mandatory for any candidate

`ROSENFELD_REVIEW_v1` §4 and `SEARCH_REDUCTION_v5` §4. Any proposed mechanism must predict:

| `k` | must fail at | must apply at |
|---|---|---|
| 3 | 5 | 7, 11 |
| 4 | 11 | 13, 17, 19, 23 |
| 6 | 17, 23, 29 | 13, 19, 31, 37 |
| 7 | **41** | 31, 37, 43 |

`normalised_search_v2.py` reproduces all of these. **Run it before believing any mechanism.**
`k = 5` cannot be tested by the normalised search (`n = 6` is not a prime power).

## 6. Sequencing

1. **`citation-verifier` on MSS Theorem 2.** Everything else is conditional on it. Blocking
   for grades, not for work.
2. **Measure `ω` on LR-property tuples** — the number that decides whether R1 is alive. If
   `ω` is bounded below by a positive constant, R1 is the proof; if it decays with `M`, R1
   is dead and says so cleanly. This has never been measured and is the highest-information
   single computation available.
3. Depending on 2: R1 analytically, or R2 to finish `p = 163` while R3 continues.

Pre-registration (`experiment-designer`) is required before step 2, per `CLAUDE.md` §2.

## 7. Ledger

Decided cells **2 of 135**. `n = 8` is not proved analytically. Nothing in today's session
changed the cell count, and this plan does not either.
