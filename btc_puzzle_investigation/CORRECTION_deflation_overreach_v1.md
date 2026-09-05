# CORRECTION — the deflation reading was scoped too wide; the gate is discharged; what is actually open

**Date:** 2026-08-01.
**Target:** `RESULT_jclass_B_relevance_check_v1.md` §4, graded there
`[PROVISIONAL — experiment-designer pre-registration OWED]`.
**The owed gate has now RUN** (pre-data, on the successor spec) — see
`PREREG_deflation_120deg_generic_j_v1_DEVIATIONS.md`. **The debt is discharged.**
**§1's verdict (item B retired) is unaffected and stands.** What is corrected is §4.

---

## 1. What survives, exactly

> **The 120° law is not `j=0`-specific, within scope.**

Chain, with each link's status:

| link | status |
|---|---|
| `e₂ = e₁² − χ₂(−1)p` at generic `j` (`Aut = μ₂`) | **MEASURED** 30/30, both `ε` branches, firing control fires |
| `e₃ = χ₂(−1)p·e₁`, `e₄ = p²` | **FORCED** by the closure + purity; closure verified `j`-independent (13/13 curves, all `j`, both parities) |
| conjunction ⟹ the `ζ₃` pairing | **PROVED** symbolically, `e₁,p` free (`ANALYSIS_120deg_exact_factorization_certificate_v1.md` §1) |

Scope: `p ≤ 211`, all `p ≡ 1 mod 3`, `n` odd and cyclic, 2–3 curves per prime, curve sample
self-chosen. Conditional on purity, which is `[CITED]`/untested — but **equally untested at `j=0`**,
so it does not distinguish the cases and cannot rescue `j`-specificity.

## 2. What does NOT survive — three overreaches in §4

§4 wrote: *"may be a general fact … carrying no information specific to `j=0`, to `μ₃`, or to
secp256k1"*, and framed this as deflating "a large part of the N1 line". Three separable errors:

**(a) "Carries no content the generic case lacks" is a universal negative the design cannot support.**
Per `CLAUDE.md` — *burden of proof on the closure* — a claim of this shape must name the class of
observable it closes. §4 named none. This is the failure mode
`feedback_negative_bias_enlarge_nulls_2026_07_17` describes exactly: a scoped result enlarged into a
dismissal.

**(b) The `μ₃` structure is OUTSIDE the class of observable that was tested.**
`Aut(E) ⊃ μ₃` at `j=0` acts on points by `(x,y) ↦ (ζ₃x, y)`, which induces on the discrete log
**multiplication by a single order-3 element `m ∈ (ℤ/n)*`** — measured, and it is exactly what
`mu6_reps` quotients by:

| `p` | 43 | 67 | 79 | 127 | 163 |
|---|---|---|---|---|---|
| `n` | 31 | 79 | 67 | 127 | 139 |
| `m` | 5 | 23 | 37 | 19 | 42 |
| `ord(m)` | 3 | 3 | 3 | 3 | 3 |

So `μ₃` acts **on the cell index `a`**. Every statistic in this line — T2/T3/T4, and the `e₂`
relation itself — is an `a`-**uniform** vector identity. It is therefore *structurally blind* to the
`μ₃` action: it could not have detected `j=0` content of that kind whatever the answer. A null from
a blind instrument is not a null about the object.

**(c) "Generic" was conflated with "says nothing about secp256k1".**
secp256k1 has odd prime `n`, so it lies **inside** the generic class. A law holding for all odd-order
cyclic curves holds for secp256k1. Showing a property is not `j=0`-*specific* does not remove it from
secp256k1 and is not evidence of absence there.

## 3. The methodological failure, named

The withdrawn spec proposed to settle `j`-specificity with two statistics (`e₃`, `e₄`) that are
**forced by premises the spec itself carried** — so it would have reported "deflation confirmed"
with probability 1, on zero evidence. The forcedness had already been derived in-session, *before*
the spec was written, and was not applied to it.

Two distinct lapses, worth separating because they need different fixes:
1. **Derived a fact, then designed as though it were unknown.** Fix: any premise established during
   a session must be checked against the next spec's statistics *before* the spec is frozen.
2. **A deflationary conclusion was drafted at a width the evidence never reached.** The counter-prior
   binds symmetrically — `feedback_dont_pre_evaluate_shut_thinking_2026_07_11`: audit a *disliked*
   result as hard as a liked one. A deflation is not exempt from the closure-grade bar because it is
   deflationary. This one was not audited to that bar until the gate did it.

**The gate earned its keep.** It caught, mechanically, a defect that argument in-session had produced
and then walked past — consistent with the standing record that instruction-based self-correction on
this project has a track record near zero, and that only decidable artifacts catch these.

## 4. What is actually open — the objects this exercise surfaced

1. **Purity at every embedding** (`A3`, `[CITED]`, untested). This is what T3/T4 would genuinely
   test. It is the load-bearing premise under *both* the `j=0` and generic-`j` readings, and under
   the cap chain. A spec targeting it must state the forcedness of `e₃`/`e₄` up front so a pass is
   not misread as evidence about `j`.
2. ~~**The `μ₆` action on the cell index `a`** — the sharper successor object, a *positive* target.~~
   **⚠ RETRACTED 2026-08-01, same day, by the author.** This overstated the channel in exactly the
   way §2(a) criticizes. Measured: `h_k[m·d] = h_k[d]` for `k=1,2` at `p = 43,67,79,127` (all True),
   where `m` is the order-3 multiplier of §2(b). So `V_k(ma) = V_k(a)` **identically** — the `μ₃`
   action is **FORCED and fully absorbed** into the cell construction (`mu6_reps` takes one
   representative per `μ₆` orbit precisely because of this invariance). Any correlation statistic
   across the `μ₆` action is therefore **tautologically 1**, not unprobed. Cell-index *arrangement*
   was separately probed and is NULL (`a⁻¹` pooled `z = +1.48`, `a³` `+0.06`, 9 primes,
   `RESULT_large_p_and_arrangement_v1.md`), with even-index maps already known forced-to-zero.
   **What §2(b) correctly establishes is narrower and is a statement about instrument blindness:**
   the `a`-uniform coefficient identities cannot see the `μ₃` structure.

   **⚠⚠ SECOND-ORDER CORRECTION, 2026-08-01 — the above retraction ITSELF over-corrected.**
   Its closing clause originally read *"but it is understood, not unexplored, and it is not a leak"* —
   **an unnamed closure**, naming no class of observable, i.e. the very defect §2(a) of this file
   criticizes, committed inside the retraction of an overclaim. **Withdrawn.**

   **The positive content that clause buried, restored and stated at grade:**
   > `h_k` is **FORCED** into the `μ₃`-invariant subspace: `h_k[m·d] = h_k[d]`, `m` of order 3 in
   > `(ℤ/n)*` (measured, `p = 43,67,79,127`, `k = 1,2`, all True). So the sign sequence
   > `d ↦ χ₂(y_{[d]G})` — `n−1` values in `{±1}` — is constant on `μ₃`-orbits, leaving `≈(n−1)/3`
   > free signs instead of `n−1`. **A 3× forced structural reduction in the quadratic-character
   > sequence along the group, specific to `j=0`, hence present on secp256k1.**
   > `[MEASURED — forced symmetry; 4 primes, `k=1,2`]`

   **The dismissal to refuse:** *"that is just GLV / known / worth only `√3`."* That is a statement
   about **one algorithm** (the GLV endomorphism as a scalar-multiplication speedup). It closes GLV
   as a generic attack. It does **not** close the object named here — a forced subspace constraint on
   a character sequence. Different object, different class of observable. Collapsing the two is
   exactly the failure `feedback_closure_grade_2026_07_28` names.

   **Status: OPEN.** Whether the forced subspace is exploitable is untested. No statistic in the
   record projects onto it. It is not retired.
3. **Why odd `n` is the hinge** — the even-`n` failure is a characterization, not a null: R1's
   `distinct` count grows 11 → 28 with `p`. Unexplained.
4. Unchanged and untouched: uniformity in `p` (#26, a monodromy theorem — a proof, not a
   measurement); the cap chain's first link.

## 5. Grade

| item | before | after |
|---|---|---|
| B retired (cross-`j` Aut-contrast cannot discriminate) | `[VERIFIED]` | **unchanged — stands** |
| `e₂` relation at generic `j`, 30/30 | `[PROVISIONAL — gate owed]` | **`[VERIFIED — scoped]`**, gate discharged |
| "120° law is generic / carries no `j=0` content" | `[PROVISIONAL]` | **RETRACTED as stated** → replaced by §1's narrow form |
| purity at every embedding | `[CITED]`, untested | **unchanged — now identified as the load-bearing open premise** |
