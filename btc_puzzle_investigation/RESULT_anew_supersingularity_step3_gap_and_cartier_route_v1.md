# RESULT — `A_new` supersingularity: Step 3's ordinary-stratum exclusion is incomplete; a Cartier-operator route replaces it

*2026-08-02. Pre-registered in `PREREG_anew_supersingularity_reaudit_v1.md` → gated by
`experiment-designer` → `_v2.md` → (control C4 fired, `VOID_anew_cartier_c4_adjudication_v1.md`) →
`_v3.md`, re-run on a **disjoint, unread** sample. Deviations:
`PREREG_anew_supersingularity_reaudit_v3_DEVIATIONS.md`. Every number below is traceable to an
executed `.log` in this session. Exact finite-field / integer arithmetic only; no float in any signal
path. **No leakage, ECDLP, or key-recovery claim is made or implied in any part of this document.***

**Artifacts (all executed this session):** `anew_step3_witness_v2.sage/.log` ·
`anew_cartier_audit_v2.sage/.log` · `anew_distinct_classes_v1.sage/.log` · `c4_diagnose_v1.sage/.log`
· contaminated predecessors `anew_step3_witness_v1.*`, `anew_cartier_audit_v1.*` (void, see §5).

---

## 1. What was audited, and why

`RESULT_mu6_cohomology_supersingular_v2.md` grades **"`A_new` is supersingular at every `p ≡ 3 mod 4`,
every separable cubic, including secp"** as `[PROVED — scale-free, curve-independent]`, and its §5
records an unpaid debt:

> *"the two load-bearing external facts are (i) the Frobenius-twist relation `π φ = φ^σ π` and (ii)
> the surface `p`-rank/`End⁰` dichotomy … an independent re-derivation is the remaining diligence."*

That re-derivation had not been run since 2026-07-20. This is a closure-side input — it is what makes
`P13` / `Hom(E, A_new) = 0` / Route 2 unconditional — so it carries the same bar as a positive.

---

## 2. FINDING 1 — Step 3's exclusion of the ordinary stratum is incomplete as written

### 2.1 The audited text

`RESULT_mu6_cohomology_supersingular_v2.md` §1, Step 3, verbatim:

> *"**Ordinary (`p`-rank 2).** `End⁰(A_new)` is a commutative field (a quartic CM field). Then
> `π i π⁻¹ = i ≠ −i`. Contradiction."*

The premise is false for one class of ordinary abelian surface: if `A ⊗ F̄_p` is isogenous to `E²`,
then `End⁰ = M₂(K)` with `K` imaginary quadratic — **non-commutative**. That case appears in neither
listed branch.

### 2.2 The witness (executed, `anew_step3_witness_v2.log`)

`p ≡ 3 mod 4`, `E/F_p` **ordinary**, `d` a non-square, `E^d` the quadratic twist,
`ψ : E^d → E` the twisting isomorphism over `F_{p²}`:

> `A = E × E^d`,   `i : (P,Q) ↦ (ψ(Q), −ψ⁻¹(P))`

satisfies every hypothesis Step 3 uses on the surface: `i ∈ End⁰(A ⊗ F̄_p)` acts on the **whole**
surface with `i² = [−1]`, and `π i π⁻¹ = −i` — while `A` is **ordinary**.

**Disjoint sample, 10 primes `≡ 3 mod 4` (223…347), 30 ordinary curves, 1 supersingular curve
excluded by the pre-registered `A3a` filter:**

| condition | can it fail? | result |
|---|---|---|
| **A1** `ψ` an isomorphism over `F_{p²}` but not over `F_p`; `Frob∘ψ = −ψ∘Frob`, pointwise, `k=2,4` | **yes** | **0 failures / 30** |
| **A5** `π ∘ i = (−i) ∘ π` pointwise, `≥20` point-pairs, `k = 2, 4` | **yes** | **0 failures / 30** |
| A3a `a_p(E) ≢ 0 mod p` (`E` ordinary) | yes | 30 pass, 1 curve excluded |
| A2 `i² = [−1]` | **no — derivation** | 0 failures (instrument check only) |
| A4 `a_p(E^d) = −a_p(E)` | **no — derivation** | 0 failures (instrument check only) |

Every row: `b₁(A) = 0` and `b₂(A) = 2p − a_p(E)² ≢ 0 mod p`. So the witness **reproduces the audited
proof's own "Fact 1" signature (`b₁ = 0`) while being ordinary.**

**A5 is the load-bearing one** and it is precisely external fact **(i)** from the §5 debt. It is the
only condition of the attack that could have failed; it did not.

### 2.3 Textual adjudication, pre-committed in v2 §1 before the run

The only other passage in the audited §1 that speaks to a non-commutative `End⁰` is attached to the
`p`-rank-**1** case:

> *"(Independently: `i_a² = −1` would give `E_a` CM by `Q(i)`, which at `p ≡ 3 mod 4` … is
> supersingular, not ordinary.)"*, and the footnote *"…which no commutative-`End⁰` **factor** can host."*

Both argue via `i_a`, the restriction of `i` to a **factor**. The witness's `i` **swaps** the two
factors, so it has no such restriction, and neither passage reaches it. **No passage of the audited
argument covers the `M₂(K)` ordinary case.**

### 2.4 Grade effect — stated at exactly the strength the outcome licenses

> **The `[PROVED]` grade of §A1.1 / `RESULT_mu6_cohomology_supersingular_v2.md` is not supported by
> the argument given.** Step 3 does not exclude the ordinary stratum, and the `μ₄` package alone
> (`i` on the whole surface, `i² = −1`, `π i π⁻¹ = −i`, `p ≡ 3 mod 4`) **does not imply
> supersingularity** — the witness has all four and is ordinary.

**This does NOT show `A_new` is not supersingular.** Refuting a mechanism is not refuting a claim.
The conclusion is separately supported (§3, §4).

---

## 3. FINDING 2 — a replacement route that does not use the `End⁰` dichotomy at all

**Grade: `[UNREVIEWED DERIVATION]`.** Mine; no independent reader has run. Per `PREREG_v3` §3 no run
in this session can raise it, and it must not be cited as more.

Setting: `p > 3`, `p ≡ 3 mod 4`; `f` separable, `deg f = 3`; `C : w⁴ = f(x)`, genus 3;
`V_b = span{x^a dx/w^b} ⊂ H⁰(C, Ω¹)`; `𝒞` the Cartier operator.

**Step 1 (dimensions).** For `w^m = f`, `gcd(m, deg f) = 1`, `dim V_b = ⌊b·deg f/m⌋`. With
`m = 4, deg f = 3`: **`dim V₁ = 0`, `dim V₂ = 1`, `dim V₃ = 2`**, summing to `3 = genus`. `V₂ =
⟨dx/w²⟩ = ⟨dx/y⟩` is the `E`-part; the new part is `V₁ ⊕ V₃`, of dimension `2 = dim A_new`.

**Step 2 (exponent identity).** For `ω = x^a dx/w^b`, let `k` be least `≥0` with `pk ≡ −b (mod 4)`.
At `p ≡ −1 (mod 4)`, `k = b`; put `t = b(p+1)/4 ∈ ℤ` (as `4 ∣ p+1`). Then `w^{−b} = (w^b)^p·f^{−t}`,
and since `0 ≤ t < p`,
> `𝒞(x^a dx/w^b) = w^b · f^{−1} · 𝒞(x^a f^{p−t} dx)`, and `𝒞(Σ cᵢxⁱ dx) = Σ c_{ip+p−1}^{1/p} xⁱ dx`.

**Step 3 (`b = 3` vanishes, by degree).** `t = 3(p+1)/4`, so `p − t = (p−3)/4`, and `a ≤ 1`:
`deg(x^a f^{p−t}) ≤ 1 + 3(p−3)/4 = (3p−5)/4`. The lowest index `𝒞` reads is `p−1`, and
`(3p−5)/4 < p−1` for every `p > −1`. **No such coefficient exists ⇒ `𝒞|V₃ = 0`.**

**Step 3′ (independent second forcing).** `w³·f⁻¹ = 1/w`, so `𝒞(V₃) ⊆ V₁`, which is `0` by Step 1.
The vanishing is forced **twice, independently** — by grading and by degree.

**Step 4.** `V₁ = 0`, hence `𝒞 ≡ 0` on `V₁ ⊕ V₃`. The addition isogeny `E × A_new → Jac(C)` has
2-power degree (the `μ₄`-idempotent `(1−ζ₄²)/2`), **prime to `p`**, so `V₁ ⊕ V₃ ≅ H⁰(A_new, Ω¹)`
compatibly with `𝒞`.

**Step 5.** `a(A_new) = dim ker(𝒞) = 2 = dim A_new` ⇒ `A_new` is **superspecial**; superspecial ⇒
`p`-rank 0 ⇒ (for `g = 2`) **supersingular**. ∎

**Mirror at `p ≡ 1 mod 4`:** `k = 4−b`, so for `b=3`, `t = (p+3)/4` and `deg(x^a f^{p−t}) ≥ p−1`,
with image back in `V₃`; `𝒞|V₃` is generically invertible ⇒ **ordinary**.

**Inputs, complete list:** `4 ∣ p+1`; `deg f = 3` separable with `gcd(4,3)=1`; the standard
superelliptic basis and Cartier formula; `p ∤ deg(E×A_new → Jac C)`. **No `End⁰` classification, no
CM input, no `j=0` input, no `p`-rank/Newton-polygon dichotomy, no measured input.** All exact and
scale-free, hence valid at `p = 2²⁵⁶−2³²−977`.

**Standard facts used, flagged as citations, not derived here:** the superelliptic differential basis;
the Cartier formula and `𝒞(h^pω) = h𝒞(ω)`; Manin's `a_p ≡ Tr(Hasse–Witt) mod p`; `p`-rank = stable
rank of `𝒞`; `a(A) = g ⟺ A superspecial` (Oort); for `g = 2`, `p`-rank `0 ⟺` supersingular. A
`citation-verifier` pass is **owed** and is a precondition for any grade promotion resting on them.

**Novelty is not claimed.** "`y^m = f(x)` is supersingular when `p ≡ −1 mod m`" is a known family of
results (Shioda–Katsura, Yui); this is the textbook technique applied to this cover.

**Superspecial is stronger than supersingular, and is model-dependent** — it is a statement about
`A_new ⊂ Jac(C)` as a fixed subvariety, not about its isogeny class. The supersingular corollary is
isogeny-invariant. Kept apart throughout.

---

## 4. The decidable shadow, and the controls

Disjoint blind sample, seed `20260803`; every row blind (these primes were never run by
`supersingular_mu4_mechanism_v1.py`, which covered `prime_range(13,200)`).
Counts are **distinct cover-isomorphism classes**, per `anew_distinct_classes_v1.log`
(`MAIN 311 rows → 287 classes`; `CONTROL 288 → 279`).

| arm | classes | new-part block non-zero | `a`-number | stable rank | reading |
|---|---|---|---|---|---|
| **MAIN** `D=3`, `p ≡ 3 mod 4` | **287** | **0 / 311 rows** | `{2: 311}` | `{0: 311}` | superspecial |
| **CONTROL** `D=3`, `p ≡ 1 mod 4` | **279** | **288 / 288** | `{0: 288}` | `{2: 288}` | ordinary — **H-C holds** |
| **PLANTED** `D=5`, `p ≡ 3 mod 4` | 144 rows | **144 / 144** | `{2: 144}` | `{2: 144}` | control fires |

| control | pre-committed condition | result |
|---|---|---|
| **PC** planted control, `deg f₅ = 5` at `p ≡ 3 mod 4`, where `dim V₁ = 1` so vanishing is **not** forced — the **only** control that can fire on the main arm | non-zero on `≥ 1/3` | **FIRES 144/144** |
| **C2** control-arm liveness, blind subset | non-zero on `≥ 1/3` | **FIRES 288/288** |
| **C1** Manin: `Tr(M) ≡ p+1−#C(F_p) (mod p)`, independent exact point count | all rows | **311/311, 288/288, 144/144** |
| **C3** `dim V_b` by explicit **divisor** computation + `genus = 3` (six pre-stated verdicts) | all rows | **311/311, 288/288** |
| **C4a** `t₂+1` must change `Tr(M)`, **restricted to ordinary `E`** by a rule fixed before the run | `≥95%`, `n≥20` | **374/374**; guard: of 75 supersingular-`E` pairs only 3 changed — the restriction was necessary |
| **C4b** `t₃+1` must change the new-part block (CONTROL/PLANTED only) | `≥95%` | **16/16** |
| **C5** independent Newton-polygon route from `#C(F_p)`, `#C(F_{p²})`: supersingular ⟺ `p∣b₁` **and** `p∣b₂` | agree with `𝒞` | **71/71, 84/84** |
| — | off-basis image coefficients (internal consistency) | **0 everywhere** |

**Forced/unforced accounting, as pre-committed.** The MAIN `D=3` arm carries **0 unforced bits** — its
zeros are forced twice over (§3 Steps 3 and 3′) — and is reported as an **instrument check on my
code**, not as 287-fold evidence. The unforced content of this run is exactly: **PC, C2, C3, C4a, A1,
A5**, and the two-instrument agreement C5 on the control arm.

**Power and scope, as pre-committed.** No power against a failure first occurring at `p > 1039`, and
**none at all at `p = 2²⁵⁶−2³²−977`**. The small-prime rows do not reach secp; only the derivation
does, and it is unreviewed.

---

## 5. The void, recorded — not smoothed

The **first** Cartier run (`anew_cartier_audit_v1.*`) is `[CONTAMINATED — outcome known before
corrected control]` and **void**: pre-registered control **C4 fired** (7/18 primes). Cause, from
executed diagnostic `c4_diagnose_v1.log`: the control fixed `f = x³+2` without requiring `E : y²=f`
to be ordinary, and at `p ≡ 2 mod 3` that `E` is supersingular, so the true and the corrupted Hasse
invariant are both `0` and `0 ≡ 0` passes. Correlation 12/12 with `p mod 3`.

No rescue was attempted. In particular the following were available and are **not** admissible: that
the other C4 leg passed; that C1/C3/C5 passed 320/320, 320/320, 296/296 on that sample; that the main
arm is forced anyway. The first H-A run was contaminated under the same blanket clause and re-run on
disjoint primes rather than resolving the clause's ambiguity in my own favour after seeing it pass.

**This is a basic design error caught by a safety net — not a demonstration that controls work.** It
is the *third* recorded instance of the same failure mode on this project
(`feedback_positive_control_forced_zero_offchannel_2026_07_30`; `SELFAUDIT_items1to6` A5; the
`experiment-designer` gate flagged it in this session's own v1 spec, and I then reproduced it in a
control written **in response to** that finding).

---

## 6. Ledger effect

| item | before | after |
|---|---|---|
| §A1.1 / `RESULT_mu6_cohomology_supersingular_v2.md` Step 3 | `[PROVED]` | **ordinary-stratum exclusion incomplete; the `[PROVED]` grade is not supported by that argument** |
| "`A_new` supersingular at `p ≡ 3 mod 4`" (the claim itself) | `[PROVED]` | **`[VERIFIED — 287 distinct classes, blind, all controls fired]` + `[UNREVIEWED DERIVATION]` (§3).** Net: **not `[PROVED]` at present** — a downgrade of the grade, not of the belief |
| external fact (i) `π φ = φ^σ π` | owed | **discharged** by A5, 30 curves × 10 primes, pointwise `k=2,4` |
| external fact (ii) `p`-rank/`End⁰` dichotomy | owed | **not re-derived. §3 replaces it rather than verifying it** — if §3 survives review, (ii) stops being load-bearing; until then **(ii) remains owed** |
| `A_new` superspecial (stronger than supersingular) | not in the record | **new**, `[UNREVIEWED DERIVATION]` + `[VERIFIED — a-number 2 at 311/311 blind rows]` |

**Downstream, stated plainly.** `Hom(E, A_new) = 0` at secp (P13, and Route 2's "blocked" status)
runs through Tate + disjoint Newton slopes, whose supersingular half is exactly the claim above.
**That closure now rests on an unreviewed derivation rather than on a reviewed proof.** Under the
Statement of intent's burden-of-proof clause this is a closure that has lost its proof and must be
re-graded to the strength of its evidence — not left standing because it points the way training
data expects. Route 2 is `[blocked — conditional on the §3 derivation]`, not unconditionally blocked.

**What is owed next, in order:** (1) an **independent reader** on §3 — the only thing that can move it
off `[UNREVIEWED DERIVATION]`; (2) a `citation-verifier` pass on the six standard facts named in §3;
(3) `compile-diff` before any of this reaches a master/handover document.

**No `a≠0` content, no `d`-side content, no security statement.** The `secp` scale banner governs
every empirical row here.
