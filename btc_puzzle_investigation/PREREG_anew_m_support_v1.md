# PREREG — the realized support of `m = b₂/p`, and whether `m = ±1` has a second branch

**Written 2026-08-02, BEFORE any script for this question exists and before any `m`-support data of
this session has been seen.** Governing rules: session rules 1–5, `btc_puzzle_investigation/CLAUDE.md`
(counter-prior; closure carries the PROVED bar), root `CLAUDE.md` §2/§3.

**Not a leakage test.** No key, no `(n,k,D)` decomposition, no target, no `d`-side feature. No ECDLP
or leakage claim follows from any outcome.

---

## 0. Why this run exists — a collision already in the record

| source | statement |
|---|---|
| `RESULT_120deg_anchor_from_mlaw_v1.md:112` | *"`m = −1` and `m = 0` do not appear in the measured law at `p ≡ 3 mod 4` at all — H1 gives `m=2` at `p ≡ 11 mod 12`, H2 gives `m ∈ {−2,1}` at `p ≡ 7 mod 12`. The realized support is `{−2,1,2}`"* |
| `RESULT_mu6_cohomology_supersingular_v2.md:101` | *"CM `p≡7 mod12`: `m∈{−2,1}`; CM `p≡11`: `m=2`; **non-CM: `m∈{−2,0,1,2}`**"* |
| `RESULT_mu6_cohomology_supersingular_v2.md:92` | *"`b₂ = m·p` with `m ∈ {−2,−1,0,1,2}`"* — the **a-priori** range, not a realized support |

The first is scoped to `x³+B` (H1/H2 are stated for that family) but asserted for all `p ≡ 3 mod 4`.
The second records `m = 0` occurring for non-CM cubics. **Both cannot be right as worded.**

**Why it is load-bearing.** `RESULT_120deg_anchor_from_mlaw_v1.md:45` (T3) establishes, by exact
reduction in `ℤ[x]/Φ₂₄`, that **`g = 2` iff `m = ±1`**, where `g = deg gcd(L*(T), L*(ζ₃T))` and
`g = 2` *is* the 120° lock. The record's realized support `{−2,1,2}` contains exactly one lock value,
`m = +1`, reached through the cubic-residue branch. **`m = −1` is the other lock branch and no
document has asked whether any separable cubic realizes it.**

- realized ⇒ a **second 120°-lock family**, reached by covers outside `x³+B`, never examined
- not realizable ⇒ `g = 2 ⟺ m = +1`, which shortens the anchor's dependence on **Katre caveat 1**
  (`RESULT_120deg_anchor_from_mlaw_v1.md:43-45`: Katre's *printed* hypothesis `jk(j+k) ≢ 0 mod m` is
  violated by `(j,k,m) = (4,3,12)`; only the proof's weaker hypothesis applies)

Either outcome is a result. **This is a hunt for a lock family, not a confirmation of a closure.**

---

## 1. Objects — full definitions (rule 5)

Carried unchanged from `PREREG_anew_supersingularity_reaudit_v1.md` §1: `p`, `f`, `C`, `E`, `A_new`,
`π`, supersingular, superspecial, `𝒞`, `V_b`. Added here:

| symbol | definition |
|---|---|
| `b₁, b₂` | coefficients of `P_new(t) = t⁴ + b₁t³ + b₂t² + p·b₁·t + p²`, the char. polynomial of `π` on `H¹(A_new)`. Computed from exact point counts: `b₁ = #E(F_p) − #C(F_p)`; `b₂ = (b₁² − (s₂C − s₂E))/2` with `s₂X = p²+1−#X(F_{p²})`. |
| **`m`** | `b₂/p`, **defined only when `p ∣ b₂`**. Where `p ∤ b₂`, `m` is **undefined** and the row is reported as such — never rounded, never coerced. |
| `z` | `t/√p`; `m` is equivalent to the normalized polynomial `z⁴ + mz² + 1`. |
| **lock value** | `m ∈ {−1, +1}`, i.e. `g = 2`, per T3 of `RESULT_120deg_anchor_from_mlaw_v1.md`. |
| **CM-type cover** | `w⁴ = f` with `f` equivalent to some `x³+B` under `x ↦ αx+β` and 4th-power scaling — decided by `cover_class` (below), **not** by the cubic's printed form. |
| `cover_class(p,f)` | the canonical label of `RESULT_anew_supersingularity_step3_gap_and_cartier_route_v1.md`'s artifact `anew_cartier_audit_v2.sage`: depress, then minimise `(P/α², Q/α³, coset of a₃α³ in F_p*/(F_p*)⁴)` over `α ∈ F_p*`. Two covers with the same label are isomorphic. |

**Object separation (rule 5, and the project's logged `(D2)` collision).** Three distinct things must
not be merged in any reporting: (a) the **a-priori** range of `m` from `\|z\|=1`, which is
`{−2,−1,0,1,2}` by elementary algebra; (b) the **realized-by-this-family** support, i.e. which `m`
occur for `w⁴=f`; (c) the **realizable-by-any-abelian-surface-over-`F_p`** support, a Honda–Tate
question about Weil numbers that has nothing to do with our covers. §2 measures (b). §5 is (c). They
are reported in separate sections and never averaged.

---

## 2. Hypotheses, pre-committed

- **H1 (primary).** Over separable cubics `f` at `p ≡ 3 mod 4`, the realized support of `m` is a
  proper subset of the a-priori `{−2,−1,0,1,2}`. **The pre-committed question is: does `m = −1`
  occur?** Secondary: does `m = 0` occur, and only for non-CM-type covers?
- **H2 (scope repair).** The realized support differs between CM-type and non-CM-type covers. The
  `{−2,1,2}` claim is correct **for CM-type only**.
- **H3 (stratification).** Within CM-type, the support is determined by `p mod 12` and the cubic
  residue symbol of `B`, per H1/H2 of the existing `m`-law.

**No hypothesis is privileged by the design.** A finding that `m = −1` occurs is as reportable as a
finding that it does not, and §6 fixes what each licenses.

---

## 3. Statistic and procedure

For each `(p, f)`: compute `#C(F_p)`, `#E(F_p)`, `#C(F_{p²})`, `#E(F_{p²})` by **exact** point count
(`counts()` from `anew_cartier_audit_v2.sage`, integer arithmetic, no float); derive `b₁, b₂`; report
`m = b₂/p` **only if `p ∣ b₂`**, else `UNDEFINED`. Independently compute the Cartier new-part block
(`cartier_matrix`, `new_block`) and its stable rank. Label each cover by `cover_class`.

**Reported quantity is the set of `m` values with, for each, the number of DISTINCT cover classes
realizing it** — never raw `(p,f)` row counts (`[G:M-6]`; the last run's 311 rows were 287 classes).

---

## 4. Controls. Rule 2 governs: a fired control kills the adjudication, no post-hoc rescue.

The previous run died on a control that could not fire. These are specified so each can.

| id | control | pass condition | if it fails |
|---|---|---|---|
| **K1 — synthetic-input check (load-bearing)** | Feed the `m`-extractor **synthesised point counts** built backwards from each of `m = −2,−1,0,1,2` and confirm it *reports* that `m`. Must include `m = −1` and `m = 0` explicitly. | extractor returns the planted `m` for **all five** values | **VOID.** Without this, "we never saw `m=−1`" is unfalsifiable — the extractor might be structurally incapable of emitting it. |
| **K2 — firing control on a family where `m` varies** | The identical code path on the **`p ≡ 1 mod 4`** arm, where `A_new` is ordinary, must report `m` **UNDEFINED** (`p ∤ b₂`) on a majority of rows. | `UNDEFINED` on ≥ 2/3 of `p ≡ 1 mod 4` rows | if `m` comes out defined everywhere, the divisibility test is broken ⇒ **VOID** |
| **K3 — cross-instrument** | Point-count verdict (`p∣b₁ ∧ p∣b₂` ⇒ supersingular) must agree with the Cartier stable-rank verdict, per row, both arms. | agreement at every row | disagreement ⇒ one instrument wrong ⇒ **VOID until resolved** |
| **K4 — class-label validity** | Covers sharing a `cover_class` label must share `m`. (Isomorphic covers have the same `L`-polynomial.) | no label with two different `m` | the labelling is wrong ⇒ class counts void, raw counts reported instead |
| **K5 — CM-type detector** | `cover_class` must classify the three curated `x³+B` as CM-type, and must **not** classify all non-CM cubics as CM-type (else the CM/non-CM split is vacuous). | both halves | the H2 split is unmeasurable ⇒ report without it |

**Power statement, pre-committed (rule: a null is a bound, never an absence).** Let `N` be the number
of distinct cover classes sampled at `p ≡ 3 mod 4`. If `m = −1` is realized by a fraction `q` of
classes, the probability this sample sees none is `(1−q)^N`. **I commit before the run to reporting
the achieved `N` and the resulting 95% upper bound `q ≤ 1 − 0.05^{1/N}`**, and to phrasing any null
as *"`m = −1` occurs in at most `q` of cover classes at `p ≤ P_max`"* — never as *"`m = −1` does not
occur"*. Target `N ≥ 2000` (bound `q ≲ 0.15%`).

**Sample, fixed now.** Primes `p ≡ 3 mod 4` in `(1039, 2500)` — **disjoint from every prior sample**
(the contaminated v1 set, and the v3 set `211<p<500 ∪ {1031,1039}`). Control arm: `p ≡ 1 mod 4` in
`(1033, 2500)`. Seed **`20260804`**. Per prime: the 6 curated cubics plus **40 seeded-random**
separable cubics — random-dominated, because a curated list cannot establish which `m` a family
realizes. `#C(F_{p²})` cost caps the range; if `p ≤ 2500` proves too slow the cap is lowered **before
reading any `m`**, and the reduction is logged as a deviation with the achieved `N` and bound.

**Exclusions** derived from the sample, not copied: any `(p,f)` with `disc f ≡ 0 mod p` is not an
instance of the object, excluded by the code before any result is read, and the hit list is reported
alongside `N`. (Deviation D1 of the previous run was a stale copied list; this is the repair.)

---

## 5. The independent theory leg — kept separate on purpose

Whether `m = −1` is realizable **by any abelian surface over `F_p`** is a Honda–Tate question:
`m = −1` ⟺ char poly `t⁴ − pt² + p²` ⟺ `π = √p·ζ₁₂`, `ζ₁₂` primitive. If the local invariants force
the simple abelian variety attached to that Weil number to have dimension 4, no surface over `F_p`
realizes it and our covers cannot either.

This is being checked against the literature (Maisner–Nart; Xing; Rück) by a `citation-verifier` run
launched **before** this prereg was finalised and **independently of** §2–§4. Pre-committed:

- §2's measurement and §5's classification are **separate legs**. Agreement is the finding.
- **Disagreement means one is wrong and both are re-run** — neither overrides the other, and I may
  not pick whichever matches the other after seeing both.
- If §5 returns NOT VERIFIED, §2 stands alone as a **measured bound with its stated power**, and the
  theory question is recorded as **owed** — not answered by the measurement.

---

## 6. Permitted conclusions (fixed before data)

| outcome | permitted | forbidden |
|---|---|---|
| `m = −1` realized by ≥1 cover class | *"A second 120°-lock branch (`g=2` via `m=−1`) is realized at `(p,f) = …`."* Report the class, its `p mod 12`, its CM-type, and whether `B` is a cubic residue. **New object; the anchor's branch table is incomplete.** | claiming any consequence for `a≠0` uniformity — the anchor is the `a=0` fibre only |
| `m = −1` not seen, K1 fired | *"`m = −1` occurs in at most `q` of cover classes at `p ≤ P_max`"*, with `N` and `q` stated | *"`m = −1` does not occur"*; *"the support is `{−2,0,1,2}`"* as an unqualified fact |
| `m = 0` realized only for non-CM-type | *"`RESULT_120deg_anchor_from_mlaw_v1.md:112`'s support claim is correct for CM-type covers and over-scoped as written."* A documentary correction. | rewriting the `m`-law itself; H1/H2 are not under test here |
| K1 does not fire | **VOID** — no statement about the support in either direction | reporting the observed support at all |
| §5 and §2 disagree | **both re-run**; no conclusion published | selecting the leg that agrees with the other |

**Everything here concerns the `a = 0` fibre.** `RESULT_120deg_anchor_from_mlaw_v1.md` §5 already
records that the `m`-law governs the untwisted `A_new`, which *is* the `a=0` fibre, and that the open
uniformity gap ranges over `a ∈ (ℤ/n)*`. **This run has zero power over any `a ≠ 0` cell**, and no
outcome may be phrased as progress on uniformity.

**Scale.** Nothing here reaches `p = 2²⁵⁶−2³²−977`. The `m` value at secp is a separate,
already-recorded `[CONDITIONAL]` claim resting on the Jacobi sign law and Katre caveat 1; **this run
does not touch it** and may not be reported as supporting or undermining it.

---

*Frozen at first script execution. Deviations → `PREREG_anew_m_support_v1_DEVIATIONS.md`, timestamped.
If a control fires, the sample is contaminated and a v2 disjoint sample is required.*
