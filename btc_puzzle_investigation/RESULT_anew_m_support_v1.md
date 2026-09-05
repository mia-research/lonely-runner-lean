# RESULT — the realized support of `m = b₂/p`: `m = −1` is not realized by this family; the CM support is exactly `{−2,1,2}` by complete census

*2026-08-02. Pre-registered `PREREG_anew_m_support_v1.md` → `experiment-designer` gate (14 mechanical
+ 10 frame findings, 6 blocking) → `PREREG_anew_m_support_v2.md`, frozen, then run. Artifacts:
`anew_m_support_v2.sage` / `.log` (elapsed 1336 s). Every number below is traceable to that log.
Exact integer arithmetic throughout; the sole float is the power bound, named as a carve-out in the
prereg. **No leakage, ECDLP or key-recovery claim, in any part.***

---

## 1. Pre-registered outcomes — what fired

`PREREG_anew_m_support_v2.md` §5, rows 2, 3 and 4. Sample: 96 primes `p ≡ 3 mod 4` in `(1039, 2500)`,
disjoint from every prior sample; seed `20260804`; **4220 rows / 4199 distinct cover-isomorphism
classes** (CM stratum enumerated **exhaustively**, non-CM sampled at 40 per prime).

### Row 4 — the CM-type support, as a COMPLETE CENSUS

> **`[VERIFIED — complete census, 96 primes]`** At every prime `p ≡ 3 mod 4` in `(1039, 2500)`, over
> **all 380** CM-type cover classes (every class, not a sample), the realized support of `m` is
> **exactly `{−2, 1, 2}`**: `m = −2` at 94 classes, `m = +1` at 188, `m = +2` at 98, and
> **`m = 0` at 0, `m = −1` at 0.**

This is stronger than the record's corresponding claim, because the CM stratum is only `2` (at
`p ≡ 11 mod 12`) or `6` (at `p ≡ 7 mod 12`) classes per prime and all of them were enumerated. There
is **no within-prime sampling bound** on this statement.

### Row 3 — `RESULT_120deg_anchor_from_mlaw_v1.md:112` is over-scoped as written

The disputed sentence reads *"`m = −1` and `m = 0` do not appear in the measured law at `p ≡ 3 mod 4`
**at all** … The realized support is `{−2,1,2}`"*.

> **`m = 0` is realized at 930 non-CM cover classes.** The non-CM support is `{−2, 0, 1, 2}`
> (`−2`: 146, `0`: 930, `+1`: 1297, `+2`: 1446).

So `:112` is **correct for CM-type covers** (row 4, now a census) and **over-scoped as written** for
`p ≡ 3 mod 4` in general. This resolves the collision with
`RESULT_mu6_cohomology_supersingular_v2.md:101` (*"non-CM: `m ∈ {−2,0,1,2}`"*) — `:101` is right, and
this is an **out-of-sample replication** of it on a disjoint prime set, not a new measurement.

### Row 2 — `m = −1`, the primary question

> **`m = −1` is realized by NONE of the 4199 cover classes** — 0 of 380 CM (complete census) and
> 0 of 3819 non-CM (sampled).

Stated at exactly the strength the design supports, per the pre-committed power table:

| stratum | statement |
|---|---|
| **CM-type** | `m = −1` occurs at **none** of the CM classes at the 96 sampled primes — a complete census, no sampling bound within those primes. Not extrapolated beyond them. |
| **non-CM, headline** | `m = −1` occurs in **at most `q ≤ 3.07%`** of non-CM cover classes (`N_eff = 96` primes, the conservative prime-based bound) |
| non-CM, class-level | `q ≤ 0.078%` (`N = 3819` classes) — **licensed**, since the pre-committed precondition held: within-prime variation of `m` was demonstrated at **96/96** primes. Caveat: demonstrated variation is weaker than independence, so the prime-based bound remains the headline. |

**This is a bound, not an absence.** The forbidden phrasings ("`m = −1` does not occur"; any
unqualified support claim) are not used.

### Row 10 — H3 survives

Zero falsifiers: no two CM classes at one prime share `(p mod 12, χ₃(B))` and differ in `m`.

### Rows 6 and 7 — did not fire

`m` UNDEFINED on a MAIN-arm row: **0**. `m` outside `{−2,…,2}` or `b₁ ≠ 0` on a MAIN-arm row: **0**.
Either would have been VOID-and-investigate; the first would have contradicted the reviewed
supersingularity result.

---

## 2. Controls — all fired or passed

| control | result |
|---|---|
| **K1** synthetic-input: does `extract_m` *report* each `m ∈ {−2,−1,0,1,2}`? | **PASS**, all five, both test primes. Without this a null on `m = −1` would be unfalsifiable |
| **K3a** Manin's congruence on the `p ≡ 1 mod 4` arm, where `V₃ → V₃` is **diagonal** so the new-part block genuinely contributes to `Tr(M)` | **0 disagreements / 4600 rows**, and `Tr(M) mod p` takes **1055 distinct values** (needed ≥5, so a constant stub fails) |
| **K3b** `D = 5` planted arm at `p ≡ 3 mod 4`, where `dim V₁ = 1` and vanishing is **not** forced | new-part block non-zero **48/48** (needed ≥5) |
| **K4′** `cover_class` two-sided — must not merge non-isomorphic covers **and** must not split isomorphic ones | **PASS** at `p ∈ {11,19,23}` by brute-force orbit partition |
| **V1** numpy int64 counters vs the Sage reference implementation | **PASS**, 88 comparisons, 0 mismatches |
| G1 (guard) `m` UNDEFINED on the ordinary arm | 4600/4600 |
| G2 (guard) CM detector; labels with mixed `m` | curated all CM ✓, non-CM present ✓, **0** mixed-`m` labels |

**Why K3a and K3b exist.** The gate showed my first cross-instrument control was **forced**: both
instruments are constant on each arm, so a stub `srank_fake = 0 if p%4==3 else 1` — reading no curve
data at all — passes it at 100%. K3a was relocated to the arm where the new-part block sits on the
diagonal (at `p ≡ 3 mod 4` the new part is off-diagonal and can *never* contribute to the trace, so
Manin's congruence structurally cannot test it there); K3b tests that the same exponent arithmetic
returns non-zero where vanishing is not forced.

---

## 3. EXPLORATORY — not pre-registered, recorded separately

`m = +1` is realized at **1297 non-CM cover classes**. By T3 of `RESULT_120deg_anchor_from_mlaw_v1.md`
(`g = 2` iff `m = ±1`, an exact reduction in `ℤ[x]/Φ₂₄`), those classes carry `g = 2` — the 120° lock.
That the lock value is reached by covers **outside** the `x³+B` family is already implicit in `:101`'s
non-CM support, but its 120° consequence does not appear to have been drawn in the record.

**Scope, tightly.** This is an observation about the cover family `w⁴ = f`, at `p < 2500`, on the
`a = 0` fibre. It is **not** a statement about secp, **not** about `a ≠ 0` uniformity, and **not** a
law — no law-fit and no out-of-sample retest has been run on it. It goes under EXPLORATORY precisely
because a pre-registered cell fired and this is follow-up.

---

## 4. What this does NOT do

- **No outcome shortens the anchor's dependence on Katre caveat 1.** The prereg's v1 motivation
  claimed a null would do so; that branch was **struck before the run** when the independent
  Honda–Tate leg returned the opposite of my hypothesis: `m = −1` **is** realizable by an abelian
  surface over `F_p` (simple, dimension 2 — see
  `RESULT_anew_supersingularity_step3_gap_and_cartier_route_v2.md` §4). Only the theory leg could have
  shortened that dependence, and it did not.
- **Therefore the null is a fact about our family, not about abelian surfaces.** There is no a-priori
  obstruction to `m = −1`; the `m = −1` isogeny class over `F_p` is populated and, by
  Howe–Nart–Ritzenthaler Thm 10.1, contains a genus-2 Jacobian. **Why the family `w⁴ = f` avoids it is
  an open question this run does not answer** — it measures, it does not explain.
- **Nothing here reaches secp.** `p < 2500`. The `m` value at `p = 2²⁵⁶−2³²−977` remains the separate
  `[CONDITIONAL]` claim resting on the Jacobi sign law and Katre caveat 1, untouched in either
  direction.
- **Zero power over any `a ≠ 0` cell.** This is the `a = 0` fibre throughout.
- The `g = 2 ⟺ m = +1` biconditional is **not** claimed — that is a universally quantified statement
  and this is a bounded sample.

## 5. Ledger effect

| item | before | after |
|---|---|---|
| `:112` support claim | *"`m=−1`, `m=0` do not appear at `p ≡ 3 mod 4` at all; support `{−2,1,2}`"* | **correct for CM-type (now a census); over-scoped as written** — `m = 0` at 930 non-CM classes |
| `:101` non-CM support `{−2,0,1,2}` | 42 primes × 6 cubics | **replicated out-of-sample**, 96 disjoint primes, 3819 classes |
| CM-type support | measured on curated `B` only | **`{−2,1,2}` by complete census at 96 primes** |
| does `m = −1` occur in this family? | never asked | **bounded: `q ≤ 3.07%` non-CM (headline), zero of 380 CM by census** — open as to *why* |
| is `m = −1` realizable by any surface over `F_p`? | my hypothesis: no (dim 4) | **YES — simple, dim 2** (verified, `..._v2.md` §4). Hypothesis refuted before the run |

**Owed:** an explanation for the family-level avoidance of `m = −1` (the measurement does not supply
one); Xing / Maisner–Nart Table 1 as peer-reviewed primaries for `m = ±1` at `p ≡ 7 mod 12`;
`compile-diff` before any of this reaches a master or handover document.
