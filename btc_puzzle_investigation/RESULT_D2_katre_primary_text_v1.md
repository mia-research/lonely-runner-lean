# RESULT — (D2) read against Katre's primary text: caveat 1 dissolves via Prop 3′ + Prop 1(f)

> ## `[PROVISIONAL — citation-verifier gate UNAVAILABLE]`
>
> **This is the grade slot, per CLAUDE.md §2a condition 1.** The mandated `citation-verifier` pass
> **did not run**: launched 2026-07-30, terminated by an API session limit before producing any
> artifact. **This is the FOURTH citation-verifier failure on this project** (Lemmermeyer Ch. 7 twice,
> Stickelberger once on 2026-07-25, now this). Per §2a this is *gate UNAVAILABLE* (infrastructure), not
> *gate FAILED*, so the work below proceeds provisionally under all four conditions — **including
> condition 4: NO GRADE PROMOTION.** `m = 1` at secp does **not** move on the strength of this file.
>
> **Gate recorded as OWED** (condition 3): `citation-verifier` on (D2), attempted 2026-07-30, failed on
> session limit, no artifact produced. The partial output visible at termination was a fragment
> (*"Conrad's paper is exactly on point. Let me get its reference list."*) — **discarded, not used**; a
> run that did not complete is a run that did not happen.
>
> **Self-audit — what this file does NOT cover (condition 2), by §2a's layer table:**
> - **Mechanical layer — COVERED, with artifact.** What Katre's propositions state, and the arithmetic
>   `4·3·7 ≡ 0 mod 12` vs `4, 3, 7 ≢ 0 mod 12`. The primary text was read directly (PDF, §§1–4,
>   journal pp. 75–84) and is quoted verbatim below. A quote is the artifact; this layer does not need
>   isolation.
> - **Frame layer — NOT COVERED. This is the uncovered section.** The judgment that **Prop 3′ + Prop 1(f)
>   legitimately substitute for Prop 4(ii)** in our derivation is *mine*, made in the main conversation
>   with full knowledge of which answer was wanted. §2b names isolation as the mechanism against exactly
>   this class of error, and it was absent. The route is also the one the project's own predecessor file
>   pre-named as the alternative, so it is not independent of the project's framing either.
> - **Not covered: any second source.** Ireland–Rosen Ch. 14, Berndt–Evans–Williams Ch. 11, Gross–Koblitz,
>   Lang, Washington — **all unchecked.** The Conrad notes were fetched but not read. The original brief
>   asked for an *independent* source; this file supplies none.

*2026-07-30. Primary text: S. A. Katre, "Gauss-Jacobi Sums and Stickelberger's Theorem", journal
pp. 75–84, read directly. No leakage or ECDLP claim.*

---

## 1. What we needed and what the text says

**(D2) as used:** `v_𝔭(J(ω^{−a},ω^{−b})) = [s(a)+s(b)−s(⟨a+b⟩)]/(p−1)`, for `m = 12` (composite),
`f = ord_12(p) = 2`, exponent triple `(j,k,m) = (4,3,12)`.

| sub-claim | verdict | verbatim source |
|---|---|---|
| `m` composite allowed | **CLEAN** | p.81: *"Let `m` be a fixed positive integer, `p` a prime, `(p,m) = 1`. Let `f` be the order of `p` (mod `m`), so `m` divides `p^f − 1 = q − 1`."* No prime/prime-power hypothesis appears anywhere in §§3–4. |
| `f = 2` (general `f`) allowed | **CLEAN** | §3 opens (p.79) *"Let `p` be an odd prime and let `q = p^f` be a power of `p`."* Prop 2 (p.81): `s(α) = a₀+a₁+⋯+a_{f−1}`, the base-`p` digit sum over `f` digits. Summary (p.81): *"`v_{P̄}(g(ω^{−α})) = s(α) = …` the sum of digits of `α` in its base-`p` expansion."* |
| Jacobi form's hypothesis | **CAVEAT 1 CONFIRMED — and bypassable** | see §2 |

`ord_12(p) = 2` for `p ≡ 7 mod 12` (`7² = 49 ≡ 1 mod 12`), so `f = 2` is our case exactly.

---

## 2. Caveat 1 — confirmed verbatim, then bypassed

**The printed hypothesis (p.83, Proposition 4(ii)):**

> *"(Prime factorisation of Jacobi sums) Let `j,k` be integers such that `jk(j + k) ≢ 0 (mod m)`. Let
> `θ_{j,k} = Σ_{a (mod m), (a,m)=1} ([(j+k)a/m] − [ja/m] − [ka/m]) σ_a^{−1}`. Then
> `(J(χ^j, χ^k)) = ℘₀^{θ_{j,k}}` as ideals in `ℚ(ζ_m)`."*

**Our triple violates it:** `j·k·(j+k) = 4·3·7 = 84 = 7·12 ≡ 0 (mod 12)`. Exactly because `12` is
composite. **Caveat 1 is confirmed against the primary text**, not merely reported.

**The proof's hypothesis (p.84):**

> *"Let `j, k` be such that `j, k, j + k ≢ 0 (mod m)`. Then `mθ_j + mθ_k − mθ_{j+k} = m Σ_{(a,m)=1}
> ([(j+k)a/m] − [ja/m] − [ka/m]) σ_a^{−1}` so that, using Prop. 1(f), `(J(χ^j,χ^k)^m) = ℘₀^{mθ_{j,k}}`,
> where `θ_{j,k} ∈ ℤ[G]`. Hence `(J(χ^j,χ^k)) = ℘₀^{θ_{j,k}}`, by unique factorisation in `ℚ(ζ_m)`."*

`4, 3, 7` are all `≢ 0 mod 12`. **The proof covers us; the printed statement does not.**

### 2a. The bypass — Prop 4(ii) is not needed

> **Proposition 3′ (p.82).** *"(Prime factorisation of Gauss sums) For `k ≢ 0 (mod m)`,
> `(g(χ^k)) = ℘₀^{Σ_R s(kad)σ_a^{−1}}`."*  — sole hypothesis `k ≢ 0 (mod m)`.
>
> **Proposition 1(f) (p.76).** *"`g(χ₁)g(χ₂)/g(χ₁χ₂) = J(χ₁,χ₂) if χ₁χ₂ ≠ 1`."* — sole hypothesis
> `χ₁χ₂ ≠ 1`.

With `χ` of order `m = 12` (Katre's `χ = ω^{−d}`, `d = (q−1)/m`): `χ⁴` has order 3 (`= χ₃`), `χ³` has
order 4 (`= χ₄`), `χ⁷` has order 12 (nontrivial).

- Prop 3′ applies to `g(χ⁴)`, `g(χ³)`, `g(χ⁷)` — since `4, 3, 7 ≢ 0 (mod 12)`. ✓
- Prop 1(f) applies to `J(χ⁴,χ³) = g(χ⁴)g(χ³)/g(χ⁷)` — since `χ⁴χ³ = χ⁷ ≠ 1`. ✓

Composing gives ideal exponent `Σ_R [s(4ad) + s(3ad) − s(7ad)] σ_a^{−1}`, which at `a = 1`, `d = M =
(q−1)/12` is `s(4M) + s(3M) − s(7M)` — **precisely the quantity the (D3) digit computation evaluates** in
`RESULT_jacobi_sign_law_stickelberger_v1.md`. The `/(p−1)` is the ramification descent `P = P̄^{p−1}`
(p.80), converting `v_{P̄}` to `v_℘`.

> **⇒ Neither proposition on this route carries a hypothesis our triple violates.** The `jk(j+k)` form
> never enters. This is the route the predecessor file pre-named (*"or route through Prop 3′ +
> Prop 1(f)"*); it now has the primary text behind it.

---

## 3. Effect on the ledger — and the limit of that effect

| item | before | after |
|---|---|---|
| Katre caveat 1 (printed vs proof hypothesis) | described from a prior run; text unread this session | **confirmed verbatim**, and shown **bypassable** via Prop 3′ + Prop 1(f) |
| `m` composite, `f = 2` | `[CITED — verified]` from a prior run | **re-confirmed against primary text**, quotes in §1 |
| independent second source | owed | **still owed — none checked** |
| **`m = 1` at secp** | `[PROVED — modulo (D2), 3 Katre caveats]` | **UNCHANGED.** §2a condition 4 forbids promotion while the gate is unavailable. |

**Why the grade does not move even though the finding is favourable.** The load-bearing step here is a
*frame* judgment — that Prop 3′ + Prop 1(f) may stand in for Prop 4(ii) — made without isolation, by the
party that wanted the answer. §2b's evidence is that this is the layer where the frame is invisible from
inside. The mechanical layer (what the text says, and `84 ≡ 0 mod 12`) is solid and quotable; the frame
layer is not audited. Treating a favourable provisional result as a promotion is precisely the
failure §2a condition 4 exists to prevent.

**What would clear it:** (i) the `citation-verifier` pass, re-run when the session limit resets, given
this file's §2a route as the specific target; and/or (ii) a genuinely independent source — Ireland–Rosen
Ch. 14 or Berndt–Evans–Williams Ch. 11 — stating either the Gauss-sum digit-sum valuation for general
`f` or the Jacobi form without the `jk(j+k)` restriction. **Either alone suffices**; the route in §2a
means we no longer need a source that states the *Jacobi* form at all, only the *Gauss* form plus the
standard `J = gg/g` identity, which is a much weaker ask.

**Also note (not a defect, but scope):** Katre's Prop 1(f) and Prop 3′ are stated for his own
normalisation `g(χ) = −Σ χ(a)ψ(a)` and `J(χ₁,χ₂) = −Σ χ₁(a)χ₂(1−a)` (Def. 1, p.75–76 — note the **minus
signs**, and footnote 1 flagging that this differs in sign from Adhikari's article in the same
proceedings). Signs do not affect *ideal* factorisations, which is all (D2) is used for — but any future
use of these propositions for a *value* rather than an ideal must reconcile the normalisation first.
