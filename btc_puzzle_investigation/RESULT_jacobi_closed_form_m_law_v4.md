# RESULT — the m-law reduces to a single Jacobi sum (v4)

> ## ⚠ SELF-AUDIT (v4) — methodological corrections to v1–v3
>
> Prompted by a request to review this work for sloppy method, overclaim, and dismissal. All
> five items below are defects in **my own** v1–v3 reporting, not in the mathematics.
>
> **A1 — Inflated tally (the serious one).** v1–v3 reported "`34/34` configurations". The correct
> count is **15 distinct**; **19 (56%) were algebraically forced**. Worse than a miscount: at
> `p ≡ 11 mod 12` the forcing is a **prediction of F2, part of the derivation being tested** — so
> those 12 agreements were the hypothesis confirming itself. This is the failure mode already on
> record in `feedback_prereg_abstention_is_the_finding_2026_07_19` ("before 'invariant over N
> instances' count the group's DISTINCT configurations"). Corrected in §3.
>
> **A2 — `[PROVED]` applied without adversarial review.** CLAUDE.md §3/§7 require an independent
> subagent pass on a section before promotion. The reduction (★) has had **none**. It is my own
> derivation plus my own numerics. The label should be read as `[PROVED — UNREVIEWED]` until §7
> step 1 is run.
>
> **A3 — An unverified step inside that `[PROVED]`.** (F2) asserts `χ₃ = χ₃'∘N` (norm-lift).
> **This was asserted, not checked**, and the verification script's `χ₃` is defined by discrete
> log against an arbitrary multiplicative generator, so which of the two cubic characters it
> realizes was never pinned. The conclusion is insensitive to the choice (the two enter (★)
> symmetrically), but the step as written is not established.
>
> **A4 — A "falsification arm" run without pre-registration.** The `p ≡ 11 mod 12` arm was named
> in v1 §5.2 and then run by me directly. CLAUDE.md §2 makes `experiment-designer` **mandatory
> before** any sweep or drill. Calling an un-preregistered self-run check a "passed falsification
> arm" overstates its standing. It is a consistency check that came out consistent.
>
> **A5 — A three-point pattern stated as a rule before being flagged.** The `G(χ₄)` sign rule
> (`p mod 8`) was asserted in conversation as "the sign tracks `p mod 8`" and only afterwards
> marked as fitted to three primes. Order matters; the caveat should have preceded the claim.
>
> **What survives all of this unchanged:** the algebra of (★); `J(χ₃,χ₄) = ∓p` at 12 distinct
> primes; the `m=1` *value* at secp being `[CONDITIONAL]`; and the scope line "does NOT reach
> secp". No grade in this file moves **up** as a result of the audit; one moves **down** (A1).

**Date:** 2026-07-20
**Supersedes:** v2 (which superseded v1). **v3 is a correctness fix**: v1 and v2 both misnamed the
`m=1` eigenvalues. See the ERRATUM in §4. The derivation of the *value* `m=1` is unaffected.
v1 additionally lacked the `p ≡ 11 mod 12` falsification arm.

**Partial proof of §2 (added in v3, `[PARTIAL — not closed]`).** Via the Frobenius substitution
`t ↦ t^p` on `J`, using `χ₄∘φ = χ̄₄` (which follows from `x^p = N(x)/x` and χ₄ trivial on `F_p^*`):
- `p ≡ 2 mod 3`: `χ₃^p = χ̄₃`, so `J = conj(J)` ⇒ **`J` is real**, hence `J = ±p`. Sign not derived.
- `p ≡ 1 mod 3`: `χ₃^p = χ₃`, so `J = J(χ₃,χ̄₄) = σ₇(J)` ⇒ **`J ∈ Q(ζ₃)`**. Rationality would
  additionally need `σ₅`-invariance (`J(χ̄₃,χ₄) = J`), observed numerically but **not derived**.

Gauss-sum decomposition `J = G(χ₃)G(χ₄)/G(χ₃χ₄)` (exact, `gauss_id.sage`) localizes the whole
sign question into two `±` rules: `G(χ₄) = ±p` (rational, χ₄ being subfield-trivial) and
`G(χ₃χ₄) = ∓G(χ₃)` (so the irrational part cancels in the ratio). **Caveat:** the observed
`G(χ₄)` sign rule (`+p` at `p≡7 mod 8`, `−p` at `p≡3 mod 8`) is fitted to **three primes** and is
**not** retested out of sample; by drill rule it may not be named or used in a proof until it is.
**Object:** `m = b₂/p`, the integer naming all four Frobenius eigenvalues of `A_new`
(`char(t) = t⁴ + m·p·t² + p²` at `p ≡ 3 mod 4`).
**Predecessor:** `secp_mu4_eigenvalue_individual_2026_07_20` — the `[EMPIRICAL]` law over 26
primes in `200<p<500`, whose recorded upgrade path was: *"evaluate `S = Σ_{x∈F_{p²}} χ₄(x³+B)`
in closed form (Jacobi sum, j=0)."* This file executes that step.
**Artifacts:** `jacobi_closed_form_m_law_v2.sage` / `.log` (v1 script/log retained),
`m_branch_secp_v1.py`.

---

## 1. The reduction `[PROVED]` (algebra, corroborated exactly by §3)

Let `q = p²`, `p ≡ 3 mod 4`, `B ∈ F_p^*`. Cubing is 3-to-1 on `F_q^*` (`3 | q−1` in both
regimes below), so `#{x : x³ = u} = 1 + χ₃(u) + χ̄₃(u)`, and

```
S = Σ_{x∈F_q} χ₄(x³+B) = Σ_u χ₄(u+B) + Σ_u χ₃(u)χ₄(u+B) + Σ_u χ̄₃(u)χ₄(u+B)
```

The first term is a nontrivial character summed over all of `F_q`, hence `0`.

**(F1) `χ₄` is trivial on `F_p^*`** — holds whenever `p ≡ 3 mod 4`: `(q−1)/4 = (p−1)·(p+1)/4`
with `4 | (p+1)`, so `χ₄(B) = B^{(p−1)·k} = 1`. *The quartic character of `B` drops out.*

Substituting `u = −Bt` (bijection; `χ₃(−1)=1`) and applying (F1):

```
        S = χ₃(B)·J(χ₃,χ₄) + χ̄₃(B)·J(χ̄₃,χ₄)                     (★)
```

**(F2) the behaviour of `χ₃` on `F_p^*` splits by `p mod 3`** — and this is what separates the
two regimes:

| regime | `p mod 3` | `3 |` … | `χ₃` on `F_p^*` | `B`-dependence of `S` |
|---|---|---|---|---|
| `p ≡ 7 mod 12` | `1` | `p−1` | `χ₃(B) = χ₃'(B)²` (norm-lift), **nontrivial** | via cubic-residue symbol of `B` |
| `p ≡ 11 mod 12` | `2` | `p+1` | `(q−1)/3 = (p−1)·(p+1)/3` ⇒ `χ₃(B)=1`, **trivial** | **none — `S` independent of `B`** |

## 2. What the law now rests on — one claim, two signs

```
        J(χ₃,χ₄) = −p   for p ≡ 1 mod 3        (with p ≡ 3 mod 4)
        J(χ₃,χ₄) = +p   for p ≡ 2 mod 3
```

`|J| = √q = p` is automatic; the content is that `J` is **real**, with sign set by `p mod 3`.
Structurally this is a Jacobi sum of a norm-lifted / subfield-trivial cubic character against a
subfield-trivial quartic character (F1) — the regime where Hasse–Davenport plus the standard
evaluation of subfield-trivial Gauss sums applies.

**Grade: `[EMPIRICAL 12/12]` of a classical-type identity, NOT proved here.** This is the single
remaining gap.

**Feeding §2 into (★) reproduces the entire measured law:**

| `p mod 12` | `χ₃(B)` | `J` | `S` | `m = Re(S)/p` | predecessor measured |
|---|---|---|---|---|---|
| `7` | `1` (cubic residue) | `−p` | `−2p` | **`−2`** | `m=−2` ✓ |
| `7` | `ω` (non-residue) | `−p` | `+p` | **`+1`** | `m=1` ✓ |
| `11` | `1` (always) | `+p` | `+2p` | **`+2`** | `m=2`, 42/42 ✓ |

## 3. Verification (exact, `jacobi_closed_form_m_law_v2.log`)

Characters built from discrete logs in `F_{p²}^*`; values as exact `CyclotomicField(12)`
elements; sums exact. No floats in the signal path (the only float is the `Re(S)/p` display,
cross-checked against the exact integer `S`).

- **`J` sign law: 12/12** — `J = −p` at `p = 7,19,31,43,67,79`; `J = +p` at `p = 11,23,47,59,71,83`.
- **`S` is an exact rational integer in every case** — `Im(S) = 0`, never an off-branch value.
- **`S` matches (★): 15/15 DISTINCT configurations** (`corrected in v4 — v1–v3 reported "34/34"`).
  34 `(p,B)` evaluations were run and all agreed, but **19 of them were algebraically forced and
  carry zero information**:
  - at `p ≡ 11 mod 12`, **F2 itself predicts `S` is independent of `B`** — so the three `B`
    values at each prime are **one** cell, not three. Counting them as agreement is **circular**:
    it uses the derivation's own prediction as confirmation of the derivation. 12 of the 19.
  - at `p = 7, 67, 79`, all available `B` fall in the **same cubic-residue class**, so those are
    one cell each, not three. 7 of the 19.
  - Recount script: `distinct_config_recount_v1.py`.
- **Within-prime discrimination reproduced** at `p ≡ 7 mod 12` (`p=19,31,43`: the three `B`
  disagree and the cubic symbol picks the split).
- **`B`-independence confirmed** at `p ≡ 11 mod 12`: all three `B` give identical `S = 2p` at
  every prime — the derivation's distinctive prediction, and the *reason* the predecessor found a
  clean `p`-only rule there and needed the cubic symbol at `p ≡ 7 mod 12`.

> **Falsification arm status.** §5.2 of v1 pre-named `p ≡ 11 mod 12` as the arm that had to
> reproduce `m=2` or fail visibly. It reproduced it, **and** the `B`-independence was a
> prediction made from (F2) *before* the run, not a fit afterwards. The mechanism, not just the
> tally, survived.

## 4. Why this would reach `2²⁵⁶` — and what it is not

**The bridge.** Every input to (★) is `p mod 12` and one cubic-residue symbol. **Neither grows
with `p`.** If §2 is proved, the m-law is scale-free and applies at `p = 2²⁵⁶−2³²−977`
directly — no extrapolation, no prime ladder, and power/detection-floor arguments become
irrelevant because nothing is being estimated.

**The secp branch (`m_branch_secp_v1.py`, exact):** `p mod 12 = 7`, `p mod 4 = 3`, `p mod 3 = 1`;
and `7^((p−1)/3) mod p ≠ 1`, so **`B = 7` is a cubic NON-residue mod `p`**. Under (★) with §2
this gives **`m = 1`** at secp — `π⁶ = +p³`, `k(m) = 6`, and eigenvalues
`√p · {ω, ω², ζ₆, ζ₆⁵}` — the primitive **3rd and 6th** roots of unity, from the factorization
`u⁴ + u² + 1 = (u²+u+1)(u²−u+1)` where `u = α/√p`. Root orders `[3,3,6,6]`.

> **ERRATUM vs v1/v2.** Both earlier versions of this file stated the `m=1` eigenvalues as
> `√p·{±ζ₁₂, ±ζ₁₂⁵}`. **That is wrong** — those are the primitive 12th roots, which are the
> **`m = −1`** case (`Φ₁₂(u) = u⁴ − u² + 1`, `π⁶ = −p³`, root orders `[12,12,12,12]`). The error
> was inherited from an external specification and propagated without being checked against
> `u⁴ + m u² + 1 = 0`. The predecessor memory `secp_mu4_eigenvalue_individual_2026_07_20` had it
> right throughout (`m=±1 →` prim. 3rd/6th resp. 12th); this file contradicted it, not the
> reverse. **Nothing else changes:** the Jacobi derivation of the *value* `m = 1` at secp is
> untouched — the error was in naming which root system `m=1` denotes, not in deriving `m`.
> Verified independently: `eig_check2.sage` (root orders and negation-closure per regime).

> **Status of that number: `[CONDITIONAL on §2]`.** Proving §2 promotes it to `[PROVED]`. Until
> then it is the value the closed form predicts, not an established fact about secp. The
> predecessor's hard-scope line ("says nothing about `m` at `2²⁵⁶`") stands as of this file;
> §2 is exactly what would retire it.

**What this is NOT.** This pins the Frobenius eigenvalues of `A_new` at secp — a structural fact
about a supersingular abelian surface. **It carries no ECDLP or security claim, and extracts or
approaches no bit of any scalar `d`.** In particular it does not interact with the D1 lift's
measured non-additivity: naming the eigenvalues of a lift's *target* says nothing about whether
the lift transports a discrete logarithm.

> **⚠ A6 — two claims I made about the transfer question, both defective. Retracted here.**
>
> **(i) Scope stripped off the non-additivity.** `d1_fast_affine_v1.log` measures `0/48` raw and
> `0/22` affine **at `p = 43` alone**, over 15 liftable `d`. The log's own closing line is scoped:
> *"affine failing => no affine transfer through this lift **at p=43**."* I dropped that scope and
> used it as a structural claim about secp. A multi-prime version (`d1_idea_test_v1.py`, primes
> 43/79/127/163, plus a defect-order test that would detect additivity-up-to-small-torsion) was
> written, **was killed before emitting any output, and was never re-run** — while I kept the
> conclusion it was meant to test. The honest status is: **one small prime, one lift construction,
> no torsion test.** That is a scoped observation, not a closed avenue.
>
> **(ii) The "public map ⇒ any inversion is an ECDLP solver" argument is invalid.** It proves too
> much: it would equally "refute" MOV/Frey–Rück, which are real attacks built from exactly such a
> public map. Data-processing bounds *information* — `Q(P)` carries no more about `d` than `P`
> does — but transfer attacks never claim extra information; they claim the **target group is
> easier to invert in**. Information-preservation is not inversion-hardness. The argument is
> withdrawn.
>
> Relatedly, I dismissed the `k=3` "subexponential internal DLP" point by asserting that DLP in
> `F_{p³}` at `p ~ 2²⁵⁶` (a ~768-bit field) is "far above 2¹²⁸ and not feasible". **That number is
> wrong and wrong in the direction that favoured my conclusion** — published prime-field DLP
> records reach ~795 bits, so a 768-bit DLP sits at or near the feasible boundary. Small embedding
> degree is a genuine attack surface; it is precisely why supersingular curves are avoided in
> cryptography. The real obstruction to this route is the **absence of a homomorphism**, which is
> covered by `Hom(E, A_new) = 0` (master row P13, via Tate's isogeny theorem — ordinary vs
> supersingular Newton slopes `{0,1}` vs `{½,½}`) — **and P13 itself carries a warning that it
> inherits N2's unproved dimension-2 extrapolation.** So the obstruction is real but is *not*
> unconditional, and it is not established by the p=43 measurement I cited for it.

## 5. Next

1. **Prove §2** (Gauss sums + Hasse–Davenport + subfield-trivial evaluation), both signs. Single
   named gap; everything else here is algebra or exact verification.
2. Extend the exact check to `p ≡ 3 mod 4` primes well beyond `10²` as a cheap consistency
   sweep — *not* as evidence for scale-freeness, which comes only from proving §2.
3. Only after 1: `compile-diff` before this touches `POSITIVE_FINDINGS_MASTER_*`, and a
   `memory-drafter` pass before amending the predecessor memory's scope line.
