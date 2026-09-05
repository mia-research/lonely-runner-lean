# RESULT — the `μ_m` vanishing law: the pairing mechanism survives out-of-sample; the uniform vanishing is `(4,3)`-specific, not an `m = 4` fact

*2026-08-02. Pre-registered `PREREG_mu_m_vanishing_law_v1.md` → `experiment-designer` gate (16
findings, **5 blocking, 1 critical**) → `PREREG_mu_m_vanishing_law_v2.md`, frozen, then run.
Artifacts: `mu_m_vanishing_law_v1.sage` / `.log` (elapsed 15580 s wall; ~57 min CPU — the machine
idled between sessions, so wall overstates the work). Exact integer / finite-field arithmetic
throughout. **No leakage, ECDLP, or hardness claim, in any part — see §5.***

---

## 0. What the gate changed, because it changes what this result means

v1's design was **void**: it defined `p`-rank as the Cartier stable rank and then *constructed* the
Cartier matrix block-graded, so `p`-rank `≤ S` held **by construction** — for every `f`, every `p`,
and every coefficient value including wrong ones (4000 random graded fills max out at exactly `S`;
at `p ≡ −1` the grading is insensitive even to a sign error in the recipe). Statistic and bound were
the same object twice.

> **Therefore: P1 is tested here ONLY against the point-count `p`-rank** — the Newton polygon of the
> `L`-polynomial built from `#C(F_{p^n})`, `n = 1…g`. **The Cartier stable rank cannot violate `S`
> and is reported below as a consistency check on the code, never as evidence.**

---

## 1. P1 — the pairing mechanism survives, on the independent readout

> **`[VERIFIED — 408 covered rows]`** Point-count `p`-rank `≤ S(m,d)` at **every** covered row.
> **0 violations.**

| `(m,d)` | genus | `S` | `S_new` | C1 rows | attaining `S` | P2 rate |
|---|---|---|---|---|---|---|
| (4,3) anchor | 3 | 1 | **0** | 160 | 146 | 0.91 |
| (5,3) | 4 | 2 | 2 | 16 | 16 | 1.00 |
| (3,4) | 3 | 2 | 2 | 152 | 145 | 0.95 |
| (3,5) | 4 | 2 | 2 | 48 | 46 | 0.96 |
| (4,5) | 6 | 4 | 2 | 16 | 11 | 0.69 |
| (8,3) | 7 | 3 | 2 | 8 | 8 | 1.00 |
| (7,3) | 6 | 2 | 2 | 8 | 8 | 1.00 |
| **(5,4)** | 6 | 2 | 2 | **0** | — | **instrument-internal — no independent weight** |

**P2 (generic equality) holds at every covered `(m,d)`**: all rates `≥ 0.69`, above the
pre-committed `0.5`. Rates are reported per `(m,d)` with denominators, never pooled, as pre-committed.

**Scope, as pre-committed.** `(5,4)` has **no** point-count coverage (its smallest eligible prime is
`p = 19`, `19⁶ ≈ 4.7·10⁷`, over budget). Its Cartier readout is forced and carries **zero independent
weight**; the P1 conclusion is **not** extended to it.

**What this is a test of.** The pairing `b ↔ m−b` was derived on `w⁴ = f`, `deg f = 3`. It is
confirmed here at `m ∈ {3,5,7,8}` and `d ∈ {3,4,5}` — **outside the family it came from**, on an
instrument that could have contradicted it. That is an out-of-sample test of the reviewed derivation's
Step 3′, and it passed.

## 2. P3 — CONFIRMED, and it corrects my own earlier claim

> **`[VERIFIED — 400 rows at (5,3)]`** The `{2,3}` summand of the `p`-divisible group of `Jac(w⁵ = f)`
> has stable rank **2 in 387 of 400 rows, 0 in 13** — i.e. it is **generically ordinary**.
> **Distribution is exactly `{0, 2}`; no other value occurs**, as pre-registered.

So at `(m,d) = (5,3)` the new part is **not uniformly supersingular** — in contrast to `(4,3)`, where
it always is.

**Why the readout is binary — a derived fact, and the reason my first control "failed".** On a pair
`{b, m−b}` with `b ≠ m−b`, the stable rank is `rank((BA)^N) + rank((AB)^N)`, and those two are equal.
**The contribution of every non-self-paired pair is therefore even.** My initial K-plant tried to plant
stable rank 1 and got 0 back; that was the *plant* asking for an unachievable value, not the readout
failing. With `dim V₂ = dim V₃ = 1` at `(5,3)`, the only possibilities are `0` and `2`.

**Correction to `RESULT_anew_superspecial_consequences_v1.md` §3.** That file said the vanishing is
special to `m = 4, deg f = 3` and contrasted `m = 5` with *"`m = 4`"*. **The `m = 4` phrasing is
wrong**, and the document's own table refutes it: `(4,5)` has `S_new = 2 > 0`. Executed check:

> **`(4,3)` is the only row in the sampled table with `S_new = 0`** — and `(6,5)` also has
> `S_new = 0`, so the phenomenon **recurs** outside `m = 4`. The governing condition is
> **`min(b, m−b)·d < m` for every `b` coprime to `m`** — a joint `(m,d)` condition, `d`-dependent, not
> an `m = 4` fact.

## 3. Controls — all passed, and each could have failed

| control | result |
|---|---|
| **C1** point-count `p`-rank (the only instrument that can test P1) | 408 rows, **0 violations** |
| **C4a** generalized-`m` code must reproduce the `m = 4` matrix **entrywise** | **PASS** — 25 comparisons, 0 mismatches |
| **K-plant** readout must report a planted stable rank, for every achievable value | **PASS** (after the plant was corrected to plant only achievable — i.e. even — values) |
| **K-attain** pipeline must *reach* `S` at least once per `(m,d)` | **PASS** — every `(m,d)` has attaining rows, so none is instrument-suspect |
| Cartier stable rank `> S` | **0** — as it must be. **Forced by construction; reported as a code check, NOT as evidence** |

**Two bugs caught by my own smoke tests before the run, both recorded:** the `exec` loading the `m=4`
reference silently overwrote this script's `PMAX` and `SEED` with that file's values (the polluted run
was discarded and an assert guard added — `PMAX == 200 and SEED == 20260805`); and the K-plant defect
above. Neither is an engineering success story; they are ordinary errors that cheap checks caught.

## 4. Ledger effect

| item | before | after |
|---|---|---|
| the pairing mechanism `b ↔ m−b` (Step 3′ of the reviewed derivation) | tested only on `w⁴=f`, `d=3` | **survives out-of-sample**, `m ∈ {3,5,7,8}`, `d ∈ {3,4,5}`, 408 rows, independent readout, 0 violations |
| `p`-rank `≤ S(m,d)` at `p ≡ −1 (mod m)` | conjecture | `[VERIFIED — 408 rows]`. **Not proved** — the bound argument is sketched in the prereg and has been neither written out nor reviewed |
| "the `m = 4` vanishing" | stated as an `m = 4` fact | **wrong — `(4,3)`-specific.** `(4,5)` has `S_new = 2`; `(6,5)` has `S_new = 0`. Condition: `min(b,m−b)·d < m` for all `b` coprime to `m` |
| `m = 5` new part | predicted not uniformly supersingular | **CONFIRMED**, 387/400 ordinary, readout binary `{0,2}` |
| `(5,4)` | — | **no independent coverage; carries no weight** |

## 5. Scope — binding

- **Pure curve arithmetic.** Nothing here is a hardness or ECDLP statement. The prereg's §6 explicitly
  struck the phrase *"not uniformly **easy**"* used in an earlier draft, because it asserts
  supersingular = easy — the exact translation being forbidden. The object-level statement is: **the
  `{2,3}` summand has `p`-rank 2.** No hardness reading is named, not even to deny it.
- **Nothing reaches `p = 2²⁵⁶−2³²−977`.** `p ≤ 200` here. The derivation is scale-free; this run is not.
- Nothing about the `a ≠ 0` uniformity gap, nothing about any `d`-side object.
- **N4 / Route 3 untouched**, as pre-committed for every outcome.
- **The downstream that a violation *would* have hit** (`Hom(E,A_new)=0` / P13 / Route 2's "blocked"
  grade) is **unaffected** — there was no violation. Their grade is unchanged from
  `RESULT_anew_supersingularity_step3_gap_and_cartier_route_v2.md`.

**Owed:** a written, reviewed proof of the `p`-rank `≤ S` bound (currently a sketch); point-count
coverage for `(5,4)`; and a faster counter — `count_C` exponentiates per field element (`O(log q)`
each), which is what made this a ~57-minute CPU run; a per-field power-residue table would cut it
several-fold.
