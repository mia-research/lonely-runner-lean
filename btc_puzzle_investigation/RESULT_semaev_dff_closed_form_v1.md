# RESULT — the Semaev first-fall degree in this harness has a CLOSED FORM: `d_ff = max(2^{m−1}, |V|) + (m−1)·2^{m−1}`. It carries no arithmetic content, and the "m=4 wall" was `Dmax=30 < 32`.

**Date 2026-09-02. Grade: `[PROVED — derivation]` + `[VERIFIED — 12/12 measured points, exact]`.**
Scripts: `n7_dff_vsize_regime_v1.sage` (m=2, |V|=2..8), `n7_dff_vsize_regime_m3_v1.sage` (m=3,
|V|=3..7), both `+.log`. Signal path: the project's own `semaev_elimination_v1.macaulay_stats`
(exact GF(p) integer ranks). Audits `RESULT_semaev_structure_firstfall_vs_m_v2.md`. Ledger: **M35**.
Model scale; **no secp claim of any kind** — the point of this document is that the statistic in
question has *no* arithmetic content to transfer.

---

## 1. The derivation

Two facts about the harness, both verified here:

1. **The support is the dense box.** `supp(S_{m+1}(x;τ)) = [0,D]^m` with `D = 2^{m−1}`
   (`|supp|` = 9 = 3², 125 = 5³, 6561 = 9⁴ — measured). Hence the maximal-total-degree monomial
   `x_1^D···x_m^D` is **unique**: every polynomial on that support has the same leading form up to
   scalar.
2. **Nothing can fall early.** `macaulay_stats` skips a generator until its own degree
   (`if df > D: continue`), and the field equations `g_i = ∏_{v∈V}(x_i − v)` alone form a **regular
   sequence** — the harness's own calibration `CAL_A` requires `None`, re-measured `null` at every
   cell in this run.

So the first fall is the minimal S-pair between `LF(P) = x_1^D···x_m^D` and some `LF(g_i) = x_i^N`,
`N = |V|`:

    lcm(x_1^D···x_m^D, x_i^N) = x_i^{max(D,N)} · ∏_{j≠i} x_j^D

> ### `d_ff = max(2^{m−1}, |V|) + (m−1)·2^{m−1}`

(The step "first fall = minimal S-pair lcm degree" is the standard first-fall argument; it is
*verified* here at every point rather than re-proved from scratch.)

## 2. Verification — 12/12, exact, including a non-obvious flat

**m = 2** (`D = 2`, `deg P = 4`, p=307), predicted `max(2,N)+2`:

| `\|V\|` | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|
| predicted | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
| **measured** | **4** | **5** | **6** | **7** | **8** | **9** | **10** |

**m = 3** (`D = 4`, `deg P = 12`, p=307) — **out-of-sample**, predicted `max(4,N)+8`:

| `\|V\|` | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|
| predicted | 12 | **12** | 13 | 14 | 15 |
| **measured** | **12** | **12** | **13** | **14** | **15** |

The **flat at `\|V\| = 3, 4`** is the discriminating prediction — `d_ff` is *insensitive* to the
factor base while `N ≤ D`, then rises one-for-one. A generic "bigger system ⇒ higher degree" story
does not predict a plateau. `CAL_A = None` at all 12 cells.

**Consistency at m=4:** `max(8,4)+24 = 32`. The v2 run used `Dmax = 30` ⇒ `CENSORED (>30)` was
**arithmetically guaranteed before the run started**. `m=5` gives `16 + 4·16 = 80`; `m=6` gives
`32 + 5·32 = 192` — by hand, no Macaulay.

## 3. What this means for the three readings in `RESULT_semaev_structure_firstfall_vs_m_v2`

| reading there | status now |
|---|---|
| "the first-fall degree is a **forced combinatorial invariant of the support**" — zero variance over 24 random draws per m, two primes | **CORRECT, and now explained**: all draws share the unique top monomial, so all share the S-pair. The zero variance is the *signature* of the closed form, not evidence about Semaev. |
| "m=4 **CENSORED (>30)** … wall-clock 114 min … the §XI.4 wall" | **Not a wall.** The value is 32 and `Dmax` was 30. 114 minutes measured a number computable by hand. |
| "growth 4 → 12 → >30 … consistent with `d_ff` tracking `2^{m−1}` — **the non-subexponential direction**" | **MUST BE WITHDRAWN as an inference about ECDLP.** It reads a hardness conclusion off a quantity fixed by the support's top corner and `\|V\|`. |

## 4. The statistic cannot test the Petit–Quisquater assumption — in either direction

In the cryptographically relevant regime the factor base is `|V| ≈ p^{1/m} ≫ 2^{m−1}`, so
`max(D,N) = N` and

    d_ff ≈ |V| + (m−1)·2^{m−1}   —   LINEAR in the factor base size.

`d_ff` therefore **can never be low**, for any curve, any prime, any `m`. A statistic that is
bounded below by `|V|` by pure combinatorics cannot discriminate the first-fall-degree assumption.

**Root cause (structural, not a bug):** including `∏_{v∈V}(x_i − v)` as an explicit degree-`|V|`
generator *manufactures* the S-pair that sets `d_ff`. Actual Semaev index calculus does not impose
the factor-base restriction that way. **This is a statement about the harness's system, not about
the literature's first-fall degree.**

## 5. What is NOT settled

**The crux is untouched.** The subexponentiality question lives in the **solving degree**, not the
first fall. At m=3 the symmetrised system already shows blind exact `d_gb` **6 → 2**
(`RESULT_semaev_symmetric_reduction_lastfall_v2`), while its **solving degree is censored > 34** —
that censored number is the one that matters and it remains unmeasured. Nothing here bears on it.

**Also not settled:** N13's μ₃-graded syzygy m=4/5 arm (a different object); whether a system
*without* explicit field-equation generators has an informative `d_ff`.

## 6. Harness defect found

`semaev_structure_firstfall_vs_m_v2.py` has **no `if __name__ == "__main__"` guard** — importing it
executes `main()`, launching the full ladder including the ~114-minute m=4 arm. Triggered
accidentally this session and killed. Any future import of that module must be preceded by adding
the guard.
