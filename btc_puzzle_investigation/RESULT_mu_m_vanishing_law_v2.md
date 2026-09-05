# RESULT v2 — `μ_m` vanishing law, RERUN with the complete control set (SUPERSEDES v1)

*2026-08-07. `PREREG_mu_m_vanishing_law_v3.md`, frozen before execution. Artifacts:
`mu_m_vanishing_law_v2.sage` / `.log` (elapsed 4104 s). Supersedes
`RESULT_mu_m_vanishing_law_v1.md`, whose control set was incomplete — see
`AUDIT_mu_m_vanishing_law_run_v1.md`. Exact integer / finite-field arithmetic. **No leakage, ECDLP or
hardness claim, in any part.***

---

## 1. Why v1 was superseded

Three controls specified in `PREREG_..._v2.md` §3 were **not implemented** in the v1 run: **C2** (the
wrong-pairing firing control), **C4b** (the anchor), and the **cross-instrument comparison** — v1's
C1 tested `pc > S` only, so `prank_pointcount`, the readout carrying the entire result, was
**unvalidated**. An unrun control is not a passed control. v1's sample is
`[CONTAMINATED — controls completed after outcome known]`; this rerun uses fresh `f` (seed `20260806`
vs `20260805`; primes necessarily overlap since the schedule is fixed by the congruence and budget).

## 2. Controls — all seven, every one asserted

| control | result |
|---|---|
| **C1a** point-count `p`-rank `≤ S` | **408 rows, 0 violations** |
| **C1b** point-count `p`-rank **`==`** Cartier stable rank | **408 rows, 0 disagreements** — *the check v1 never did* |
| **C2** wrong-pairing arm must mispredict | **FIRES — 5/5 eligible cells**, mispredicting on **4/4 rows each** (`(5,3)` at `p = 7,13,17,23`; `(7,3)` at `p = 5`; each `S_true = 0 < S = 2`) |
| **C4a** entrywise `m=4` regression | **PASS** — 25 comparisons, 0 mismatches |
| **C4b** `(4,3)` anchor vs independently computed `a_p(E)` | **PASS** — 44 rows, 0 mismatches |
| **K-plant** | **PASS** |
| **K-attain** | **PASS** at every `(m,d)` |
| Cartier stable rank `> S` | 0 — **forced by construction, reported as a code check, not evidence** |

> **`ALL CONTROLS PASS: True`** — the script's own gate, which voids the run on any failure.

**C1b is the load-bearing addition.** Two instruments sharing essentially nothing (`prank_pointcount`
uses point counts + Newton's identities; `cartier_general` extracts polynomial coefficients — common
dependencies are `genus()` and the parameters) agree on **every one of 408 rows**. C4b independently
ties both to `a_p(E)` at `(4,3)`.

## 3. P1 — with the coverage qualification v1 omitted

> **`[VERIFIED]`** Point-count `p`-rank `≤ S(m,d)` at every covered row. **0 violations in 408 rows.**

**Reported with primes, not only rows** — v1 stated breadth without this, and it is the main
qualification on the result:

| `(m,d)` | genus | `S` | `S_new` | **C1 primes** | C1 rows | attaining `S` |
|---|---|---|---|---|---|---|
| (4,3) *anchor* | 3 | 1 | **0** | **20** | 160 | 149 |
| (3,4) | 3 | 2 | 2 | **19** | 152 | 148 |
| (3,5) | 4 | 2 | 2 | **6** | 48 | 45 |
| (5,3) | 4 | 2 | 2 | **2** | 16 | 16 |
| (4,5) | 6 | 4 | 2 | **2** | 16 | 11 |
| **(7,3)** | 6 | 2 | 2 | **1** (`p=13`) | 8 | 7 |
| **(8,3)** | 7 | 3 | 2 | **1** (`p=7`) | 8 | 6 |
| **(5,4)** | 6 | 2 | 2 | **0** | — | **instrument-internal, no weight** |

> **Scope, stated at the front and not buried:** the `m = 7` and `m = 8` evidence is **8 covers at a
> single prime each**. The broad coverage is `(4,3)` and `(3,4)` — the small-`m` cases. `(5,4)` has
> no independent readout at all and its Cartier numbers carry **zero** weight.

**What the test discriminates.** `p`-rank `≤ S` is a *consequence* of the `b ↔ m−b` pairing. Were the
pairing false the `p`-rank could reach `g` (3 rather than `≤1` at `(4,3)`). C2 shows `S` is specific
to `p ≡ −1 (mod m)`: at `p ≢ ±1` the true orbit bound is 0 and `S` mispredicts every row. So the
mechanism, derived on `w⁴ = f, d = 3`, **survives out-of-sample** — at `m ∈ {3,5}` broadly and at
`m ∈ {7,8}` narrowly.

**P2 (generic equality)** holds at every covered `(m,d)`: rates `0.69`–`1.00`, all above the
pre-committed `0.5`, reported per `(m,d)` with denominators, never pooled.

## 4. P3 at `(5,3)` — confirmed, with the instrument distinction v1 omitted

> **`[VERIFIED]`** The `{2,3}` summand of the `p`-divisible group has stable rank **2 in 384 of 400
> rows, 0 in 16**. Distribution is exactly `{0, 2}` — **no other value**, as pre-registered. So the
> new part at `(5,3)` is **not uniformly supersingular**, unlike `(4,3)`.

**Which instrument says what.** The 400-row distribution is `pair_ranks` on the **Cartier** matrix.
Direct independent backing is the **16** C1 rows at `(5,3)`, where total `p`-rank `= 2` and the
`{1,4}` pair is forced to `0`, forcing `{2,3} = 2`. v1 reported "387 of 400" without this split.
**What is new in v2:** C1b now validates the Cartier readout against the point-count readout on **408
rows across all covered `(m,d)`**, so the extrapolation from 16 to 400 rests on a validated
instrument rather than an unvalidated one.

**Why the readout is binary.** On a pair `{b, m−b}` with `b ≠ m−b`, the stable rank is
`rank((BA)^N) + rank((AB)^N)` and those are equal, so **every non-self-paired pair contributes an even
amount**. With `dim V₂ = dim V₃ = 1`, only `0` and `2` are possible.

## 5. The `(4,3)`-specific correction — unchanged, derived not measured

`RESULT_anew_superspecial_consequences_v1.md` §3 called the vanishing special to *"`m = 4`"*. **Wrong.**
`(4,5)` has `S_new = 2 > 0`; `(4,3)` is the only sampled row with `S_new = 0`; and `(6,5)` also gives
`0`, so the phenomenon **recurs** outside `m = 4`. Condition: **`min(b, m−b)·d < m` for every `b`
coprime to `m`** — a joint `(m,d)` condition, **`d`-dependent**. This is a derivation and does not
depend on either run.

## 6. Scope

- Pure curve arithmetic. **No hardness or ECDLP statement.** The object-level claim is: *the `{2,3}`
  summand has `p`-rank 2.* No hardness reading is named, not even to deny it.
- `p ≤ 200`. **Nothing reaches `p = 2²⁵⁶−2³²−977`.**
- Nothing about the `a ≠ 0` uniformity gap; nothing about any `d`-side object.
- **N4 / Route 3 untouched.**
- **Downstream unaffected:** a C1a violation would have unseated Step 3′ and with it the current
  support for `Hom(E,A_new)=0` / P13 / Route 2's "blocked" grade. There was none, so those grades are
  unchanged from `RESULT_anew_supersingularity_step3_gap_and_cartier_route_v2.md`.

**Owed, carried from v1:** a written, reviewed proof of the `p`-rank `≤ S` bound — it is a sketch in
the prereg, neither written out nor reviewed, so the grade is `[VERIFIED]`, **not** `[PROVED]`;
point-count coverage for `(5,4)`; and more than one prime for `m ∈ {7,8}`.

**Measured, correcting a claim of mine:** I asserted twice that a per-field power-residue table would
cut the point-count runtime several-fold. **Benchmarked at 0.4–0.6× — slower.** The counter is
unchanged and the rerun cost 4104 s.
