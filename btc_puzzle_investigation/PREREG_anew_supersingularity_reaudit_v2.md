# PREREG v2 — re-audit of the `A_new` supersingularity proof (SUPERSEDES v1)

**Written 2026-08-02, still BEFORE any script of this session has been written or run.** v1
(`PREREG_anew_supersingularity_reaudit_v1.md`) was submitted to the `experiment-designer` gate before
execution; the gate returned 8 mechanical + 11 frame findings. v2 is v1 with those repairs applied.
**v1 is retained unmodified** so the amendment is auditable. Amendment provenance is marked `[G:id]`
against the gate finding it answers.

Everything in v1 §1 (object definitions) is carried unchanged and is not repeated except where
amended. Read v1 §1 first.

---

## 0. Amendments to §1 (objects)

- **[G:F-7] `A_new` — added third ingredient, made explicit.** The identification
  `H⁰(A_new, Ω¹) ≅ V₁ ⊕ V₃` requires the addition isogeny `E × A_new → Jac(C)` to have degree **prime
  to `p`**. It does — the `μ₄`-idempotent `(1 − ζ₄²)/2` has 2-power denominator and `p` is odd — but
  v1 never said so, and `a`-number is not an isogeny invariant, so this is load-bearing, not
  cosmetic. Any statement of the H-B conclusion must list **three** ingredients, not two:
  `4 ∣ p+1`, the standard Cartier formula, **and** `p ∤ deg(E × A_new → Jac C)`.
- **[G:M-8] Symbols imported from the audited document, quoted verbatim so this file is self-contained.**
  From `RESULT_mu6_cohomology_supersingular_v2.md` §1 Step 3:
  > *"**Ordinary (`p`-rank 2).** `End⁰(A_new)` is a commutative field (a quartic CM field). Then
  > `π i π⁻¹ = i ≠ −i`. Contradiction."*

  and its parenthetical, attached to the `p`-rank-1 case:
  > *"(Independently: `i_a² = −1` would give `E_a` CM by `Q(i)`, which at `p ≡ 3 mod 4` — `p` inert in
  > `Q(i)` — is supersingular, not ordinary.)"*

  "Fact 1" = *"`b₁ = 0` at every `p ≡ 3 mod 4`"* (same document §2).
- **`f₅`** — a separable **quintic** in `F_p[x]`, `deg f₅ = 5`, `disc ≠ 0`. `C₅ : w⁴ = f₅(x)`,
  `gcd(4,5) = 1`, genus 6, `dim V_b = ⌊5b/4⌋ = (1,2,3)` for `b = (1,2,3)`. Used **only** as the
  planted control (§3, PC).
- **`s_b`** — the exponent actually used by the Cartier routine for eigenspace `b`:
  `k_b` := least `k ≥ 0` with `p·k ≡ −b (mod 4)`; `t_b := (b + p·k_b)/4`; the routine evaluates
  `f^{p − t_b}`. **At `p ≡ 3 mod 4`: `k_b = b`, `t_b = b(p+1)/4`** — so `t₂ = (p+1)/2` and
  `t₃ = 3(p+1)/4` are **different exponents**, which v1 conflated. `[G:M-1]`

---

## 1. Hypotheses (amended)

### H-A — Step 3's ordinary-stratum exclusion is incomplete

Unchanged in statement. **Decision rule replaced** `[G:M-2, F-2, F-11]`.

v1 listed A1–A4 as four verifications. Three of them cannot fail:

| v1 item | status in v2 | why |
|---|---|---|
| **A2** `i² = [−1]` | **DERIVATION, not a check.** `i²(P,Q) = (ψ(−ψ⁻¹P), −ψ⁻¹(ψQ)) = (−P,−Q)`. Uses only that `ψ` is a group isomorphism. Independent of `d`, of `p mod 4`, of ordinariness. | cannot fail |
| **A4** `b₁ = a_p(E) + a_p(E^d) = 0` | **DERIVATION.** `#E^d(F_p) = 2p+2 − #E(F_p)` is an identity ⇒ `a_p(E^d) = −a_p(E)` for every `E`, every `p`. | cannot fail |
| **A3 clause 2** `b₂ = 2p − a² ≢ 0 mod p` | **RESTATEMENT of clause 1.** `b₂ ≡ −a² (mod p)`, so clause 2 ⟺ `a ≢ 0`. | 0 additional bits |

Still run as **instrument checks on my code** and reported as such — never as evidence for H-A.

**The v2 decision rule. H-A is upheld iff both of the following pass, and neither is forced:**

- **A1** — `ψ : E^d → E` is an isomorphism over `F_{p²}` and **not** over `F_p`, with
  `Frob ∘ ψ = −ψ ∘ Frob`, verified **pointwise on ≥ 20 points** of `E^d(F_{p²})` and
  `≥ 20` of `E^d(F_{p⁴})`.
- **A5** `[G:F-2]` — **`π ∘ i = (−i) ∘ π` as maps on `A(F_{p^k})`, `k ∈ {2,4}`, pointwise on ≥ 20
  point-pairs at each `(p, E)`.** This is the hypothesis the attack actually turns on, and it is
  precisely external fact **(i)** from the audited document's §5 debt (`π φ = φ^σ π`). It can fail.
- **A3 clause 1** — `a_p(E) ≢ 0 (mod p)`, i.e. `E` is ordinary. A property of the sampled `E`, not
  forced by the construction; curves failing it are excluded and counted.

Sample: **≥ 3 primes `p ≡ 3 mod 4`**, **≥ 3 ordinary `E/F_p`** each, `E` drawn at random with fixed
seed (§4), not curated.

**[G:F-8] Textual step, pre-committed before the run.** "H-A upheld" licenses the §5 row-1 conclusion
only if, in addition, a verbatim reading of the audited §1 finds **no other passage** excluding the
`End⁰ = M₂(K)` ordinary case. The parenthetical quoted in §0 is attached to the `p`-rank-**1** case
and speaks of `i_a`, the restriction of `i` to an ordinary **factor**; the witness's `i` **swaps** the
two factors and has no such restriction. I pre-commit to recording that adjudication explicitly,
and to reporting "Step 3 survives" if any passage does cover the case.

### H-B — the graded Cartier route

Statement unchanged. **[G:F-6] Forcing structure corrected — the vanishing is forced TWICE, independently:**

1. **By grading + holomorphy alone.** `𝒞(x^a dx/w³) = w³·f⁻¹·(…) dx = (…)·dx/w ∈ V₁`, and
   `dim V₁ = 0` by (B-i). No degree count needed.
2. **By the degree count.** `deg(x^a f^{p−t₃}) ≤ (3p−5)/4 < p−1`, so no coefficient of index
   `ip + p − 1` exists.

v1 named only (2), the weaker forcing. (B-i) is therefore the load-bearing ingredient, and **C3 is
the check that matters** for H-B — see §3.

**(B-iii)** added per `[G:F-7]`: the isogeny-degree condition in §0.

### H-C — the mirror at `p ≡ 1 mod 4`

Unchanged, but its status is corrected: H-C is a **hypothesis about the object**, not merely a
control. `[G:F-5]` v1 collapsed "C2 did not fire" into a single cause (dead instrument). It has two,
and they are separated by the planted control — see §3 and §5.

---

## 2. Exponent table, stated in full so C4 has a defined target `[G:M-1]`

| arm | `b` | `k_b` | `t_b` | `f`-exponent `p − t_b` | image eigenspace `b' = 4 − k_b` |
|---|---|---|---|---|---|
| `p ≡ 3 mod 4` | 1 | 1 | `(p+1)/4` | `(3p−1)/4` | 3 |
| | 2 | 2 | `(p+1)/2` | `(p−1)/2` | 2 |
| | 3 | 3 | `3(p+1)/4` | `(p−3)/4` | **1** |
| `p ≡ 1 mod 4` | 1 | 3 | `(3p+1)/4` | `(p−1)/4` | 1 |
| | 2 | 2 | `(p+1)/2` | `(p−1)/2` | 2 |
| | 3 | 1 | `(p+3)/4` | `(3p−3)/4` | **3** |

`s = 1` throughout (`t_b < p` for `p > 3`, `b ≤ 3`, `k_b ≤ 3`). Matrix entry for
`ω = x^a dx/w^b`: coefficient of `x^{ip+p−1}` in `x^a·f^{p−t_b}`, placed at `x^i dx/w^{b'}`.
p-th roots are the identity on `F_p`.

---

## 3. Controls (amended). Rule 2 governs: a fired control kills adjudication, no post-hoc rescue.

| id | control | pass condition | if it fails |
|---|---|---|---|
| **C1** | Instrument validation, Manin: `Tr(M) ≡ a_p(C) (mod p)`, `a_p(C) = p+1−#C(F_p)` from independent exact point count. | every `(p,f)`, both arms, and the planted arm | script wrong; fix and re-run all; no verdict readable from a run where C1 failed anywhere |
| | **[G:F-3] Recorded limitation:** on the main arm `Tr(M) = M₁₁` (the `b=2` path), so **C1 validates the `E`-part code only and is blind to the new-part path.** It is not a control on H-B. | | |
| **PC** | **PLANTED MAIN-ARM CONTROL `[G:F-3]`.** Identical code path, `C₅ : w⁴ = f₅(x)`, `deg f₅ = 5`, at `p ≡ 3 mod 4`. There `𝒞(V₃) ⊆ V₁` with `dim V₁ = 1`, so vanishing is **not** forced. | **new-part block non-zero on ≥ 1/3 of `(p,f₅)` pairs** | **VOID.** If the routine returns zero where zero is not forced, its zeros on the `deg 3` main arm carry no information. This is the only control that can fire at `p ≡ 3 mod 4`. |
| **C2** | Instrument liveness on the control arm `[G:F-4]`: at `p ≡ 1 mod 4`, the `2×2` new-part block (rows/cols indexed by `{dx/w³, x·dx/w³}` in the `3×3` matrix on basis `{dx/w², dx/w³, x·dx/w³}`) is non-zero. | non-zero on **≥ 1/3 of blind `(p,f)` pairs** (§4) | see §5 — two causes, separated by PC |
| **C3** | **The load-bearing check for H-B `[G:F-6, M-7]`.** `dim V_b` by explicit **divisor** computation in Sage's function-field machinery, per `(p,f)`: `dx/w` **non**-holomorphic; `dx/w²` holomorphic; `x·dx/w²` **non**-holomorphic; `dx/w³`, `x·dx/w³` holomorphic; `x²·dx/w³` **non**-holomorphic. Plus Sage-computed `genus(C) = 3`. | all six verdicts + genus, at every `(p,f)` | (B-i) false ⇒ **H-B refuted**; report it |
| **C4** | Perturbation, **entrywise** `[G:M-1]`: recompute with `t_b → t_b + 1` and require the **matrix to change**, on the arm/entry where the corrupted exponent is used. Applied separately to `t₂` (must break C1) and `t₃` (must change the new-part block on the control arm and on PC). | both perturbations change their target | a corrupted exponent that changes nothing ⇒ the routine is not reading `t` ⇒ **VOID** |
| **C5** | Independent Newton-polygon route `[G:M-3, M-4]`: from exact `#C(F_p)`, `#C(F_{p²})` get `b₁, b₂`; supersingular ⟺ **`p ∣ b₁` AND `p ∣ b₂`** (v1's `p ∣ b₂` alone is **wrong** — a `p`-rank-1 surface can satisfy it). Compared **entrywise where possible**, verdict-level otherwise. | agreement at every pair | disagreement ⇒ one instrument wrong ⇒ **VOID until resolved** |
| | **[G:M-4] Recorded limitation:** verdict-level agreement on the main arm is **forced** under H-B and carries no discriminating weight there. C5 discriminates on the control arm. | | |

**[G:M-5] Separability exclusions, fixed before the run.** These `(p,f)` pairs have `disc f ≡ 0`
and are not instances of the object; they are excluded, by name, and the exclusion is reported with `N`:
`(7, x³+7)`, `(7, x³+2x+5)`, `(11, x³+11)`, `(31, x³+x+1)`, `(101, x³+2x+5)`.
Random draws rejecting `disc = 0` are re-drawn from the same seeded stream.

**Rule 1 restated as a void condition.** Every number in the result document must be traceable to a
line of this session's executed `.log`. Untraceable ⇒ deleted, not rounded.

---

## 4. Sampling, power, scope (amended)

- **MAIN (`deg 3`):** primes `p ≡ 3 mod 4`, `7 ≤ p ≤ 200`, plus `{211, 251, 503, 1019}`.
- **CONTROL (`deg 3`):** primes `p ≡ 1 mod 4`, `5 ≤ p ≤ 200`, plus `{257, 509, 1013}`.
- **PLANTED (`deg 5`):** the same main-arm primes, `p ≤ 251`, with 6 seeded-random separable quintics.
- **Cubics:** the record's 6, **plus 6 seeded-random separable cubics**, seed `20260802`.
- **[G:F-10] BLIND vs ALREADY-OBSERVED split — mandatory in reporting.** `supersingular_mu4_mechanism_v1.py:90`
  already ran `prime_range(13,200)` × the same 6 curated cubics on **both** arms in 2026-07-20, and
  its `.log` records the ss/ORD verdict for each. Therefore:
  - **already-observed:** 6 curated cubics × `p ∈ [13,199]`, both arms.
  - **blind:** 6 seeded-random cubics (all primes) + all cubics at `p ∈ {7, 11} ∪ {211,251,257,503,509,1013,1019}` + the entire planted arm.

  **C2's firing rate is read off the BLIND subset only.** Rates on the already-observed subset are
  reported separately and carry no adjudicative weight.
- **[G:M-6] Distinct-class counting.** `w⁴ = x³+B ≅ w⁴ = x³+B'` when `B'/B` is a cube-times-4th-power;
  at `p ≡ 2 mod 3` the three curated `x³+B` cubics collapse to **one** isomorphism class. The
  `[VERIFIED, N]` shadow must report **distinct isomorphism classes**, with the collapse counted,
  never raw `(p,f)` rows.
- **`#C(F_{p²})` compute scope, pre-committed:** C5 runs only for `p ≤ 251` (cost `~2p²`). This is a
  compute bound fixed before the run, not a post-hoc filter.
- **Power, pre-committed:** no power against a failure first occurring at `p > 1019`, **none at
  `p = 2²⁵⁶−2³²−977`**. Only the derivation is scale-free, and only if it survives.
- **Unforced accounting, pre-committed `[G:F-3, F-6]`.** Corrected from v1: the main `deg 3` arm
  carries **0 unforced bits** — every zero is forced twice over (H-B §1) and C1/C3/C5 are all forced
  or blind there. The unforced content of this run is exactly: **PC (does the planted control fire),
  C2 on the blind subset, C3's divisor verdicts, and A1/A5**. I commit to reporting the `deg 3`
  main-arm count as an **instrument check on my code**, whatever `N` turns out to be.

---

## 5. Permitted conclusions (amended)

| outcome | permitted | forbidden |
|---|---|---|
| A1 + A5 + A3a pass, **and** the §1 textual step finds no covering passage | *"Step 3's exclusion of the ordinary stratum is incomplete as written: an explicit **ordinary** surface satisfies (H1) `i` on the whole surface with `i²=−1`, (H2) `π i π⁻¹ = −i`, at `p ≡ 3 mod 4`. The `[PROVED]` grade of §A1.1 is not supported **by the argument given**."* | concluding `A_new` is not supersingular. Refuting a mechanism ≠ refuting a claim. |
| A1 or A5 fails | **VOID (implementation)** `[G:F-11]` — not "Step 3 survives" | reading a survival verdict off broken code |
| the textual step finds a covering passage | *"Step 3 survives"* | any grade change |
| **PC fires** + C1,C3,C4,C5 pass + no main-arm non-zero | H-B's **shadow**: `[VERIFIED — N distinct classes]` `𝒞 ≡ 0` on the new part at `p ≡ 3 mod 4` | grading the **derivation** on this basis `[G:F-9]` |
| the written H-B derivation additionally survives an **independent reader** | `[PROVED — UNREVIEWED]` for H-B, three ingredients named (§0) | `[PROVED]` flat; it is my own derivation |
| **PC does not fire** | **VOID** the H-B arm | reporting the main-arm zeros as confirmation |
| **C2 does not fire, PC does** `[G:F-5]` | *"instrument live; **H-C refuted** at the sampled `(p,f)`"* — a finding about the object; re-open the `p ≡ 1` arm separately | calling it instrument death |
| **C2 does not fire, PC does not** | **VOID** (instrument dead) | any statement about either arm |
| any main-arm `(p,f)` has a non-zero new-part block | **H-B retracted**, failing pair named | adjusting `t`, basis, or range after seeing which pair failed |

**Superspecial is model-dependent; supersingular is isogeny-invariant.** Kept apart in every
sentence of the result. **[G:F-1] Scope of the debt actually paid:** external fact **(i)** (`π φ = φ^σ π`)
is discharged by **A5** and only there. External fact **(ii)** (the `p`-rank/`End⁰` dichotomy) is
**not re-derived** by this run — H-B *replaces* it rather than verifying it. If H-B stands, (ii)
stops being load-bearing; if H-B falls, **(ii) remains owed** and must be recorded as still owed.

**No ECDLP, leakage, or key-recovery content in any outcome.**

---

*Frozen at first script execution. Deviations → `PREREG_anew_supersingularity_reaudit_v2_DEVIATIONS.md`,
timestamped, with reason.*
