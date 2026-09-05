# PREREG v2 — does the 120° lock track the curve's automorphism group?

**Date:** 2026-07-31. **Supersedes `PREREG_jclass_120deg_discriminator_v1.md` entirely.**
**Status: SPEC ONLY.** No `V` has been computed on any non-`j=0` curve. Nothing runs until the
`experiment-designer` gate returns on *this* file.

**Inputs folded in:** my own D1–D6 (`..._v1_DEVIATIONS.md`) and the gate's audit of v1 (D1,D2,D3,D5,
D6,D7,D9, P1, C1–C5, F1–F7). Every v1 defect is either repaired below or explicitly retired.

---

## 0. Hypothesis under test, and what this test cannot do

`RESULT_n1_120deg_exact_v1.md` finds `g₃ = deg gcd(L*(T), L*(ζ₃T)) = 2` at every surviving cell of
22 primes on `E: y² = x³ + 7`. A **mechanism hypothesis** (2026-07-31, `[CONJECTURAL]`, unreviewed)
proposes the eigenvalue multiset `{α, ζ₃α, −ᾱ, −ζ̄₃ᾱ}` is the shadow of `H¹ ≅ W_a ⊕ (W_a ⊗ ξ)`, with
the `ζ₃` originating in the curve's automorphism / CM structure.

**Three things this test does NOT do, stated first.**
1. **It does not test the decomposition.** A multiset of shape `W ⊔ ζ₃W` is compatible with a
   non-split extension; traces see only the semisimplification. **No eigenvalue-level statistic can
   distinguish them** — in particular the "operator `T` with `T·Frob = ζ₃·Frob·T`" test proposed on
   2026-07-31 is **circular**: an invertible such `T` forces the multiset to be `ζ₃`-*stable*, which
   it is not, and the nilpotent intertwiner that does exist has existence equivalent to `g₃ ≥ 1`,
   i.e. to the census statistic itself. That test is **retired, not deferred.**
2. **It does not presuppose the `End⁰` route.** Over `F_p`, `ℚ(ζ₁₂) ⊂ End⁰(A_new)` is commutative
   and commutes with Frobenius — standard CM splitting, no eigenvalue twist. Whether Frobenius
   conjugation over `F_{p³}` yields the `ζ₃` factor is **unproven and not assumed**.
3. **It tests a NECESSARY CONDITION only:** is the lock present on curves whose `Aut` lacks `μ₃`?

## 0a. Why not the `a=0` anchor  *(v1 §0a's justification was wrong — see v1 DEVIATIONS D2)*

`a = 0` is excluded from the census by construction (`0 ∉` the nontrivial character set), and
`RESULT_120deg_anchor_from_mlaw_v1.md` §5(ii) records that the anchor's load-bearing property ("each
`αᵢ` is `√p` × a root of unity") is the rigidity row **measured as destroyed by the twist**. The
discriminator must be at `a ≠ 0`. *(v1 argued this from a `p ≡ 11 mod 12` contrast that does not
exist: `j=0` is supersingular there and the census is empty.)*

---

## 1. ★ The arithmetic that dictates the arm design (measured, before any `V`)

Three structural facts, each verified exhaustively at small `p`:

**(A1) `j = 1728` can never have prime order.** `y² = x³ + Ax` contains `(0,0)`, which is 2-torsion,
so `2 | #E` for every `A`, every `p > 3`; every `j=1728` curve is a quartic twist of this form.
Verified: **29,184 `(p,A)` pairs, `5 ≤ p < 600` — zero with `#E` odd.** *(This is why v1's J1728 arm
was empty, and why v1's proposed repair — moving to `p ≡ 1 mod 12` — does not fix it: 912 pairs at
`p ≡ 1 mod 12`, still zero.)*

**(A2) `j = 1728` group structure is decided by `χ₂(−A)`.** `x³+Ax = x(x²+A)` splits completely iff
`−A` is a square, which forces `ℤ/2 × ℤ/2 ⊆ E(F_p)`. Measured, **21/21 curves**:

| `χ₂(−A)` | cofactor | structure |
|---|---|---|
| `−1` | **2** | **cyclic `ℤ/2n'`** |
| `+1` | 4 or 8 | grid `ℤ/2 × ℤ/2m` |

**(A3) ordinary `j = 0` can never have cofactor 2.** A rational 2-torsion point means `B = −c³`, and
`x³ − c³ = (x−c)(x²+cx+c²)` with discriminant `−3c²`; that quadratic splits iff `−3` is a square,
i.e. iff `p ≡ 1 mod 3` — **which is exactly the condition for `j=0` to be ordinary**. So even order
forces the *full* 2-torsion. Measured: every even `#E` at `p ∈ {37,61,73,97,109,157,181}` has
`4 | #E`, no exceptions. **`j=0` offers cofactor 1 or cofactor ≥ 4; never 2.**

> **⇒ The arms CANNOT be matched on cofactor.** `j=0` gives `{1, ≥4}`; `j=1728` gives `{2, 4, 8}`.
> The design below therefore **measures** the cofactor effect instead of eliminating it (§2, JGEN).

## 2. Arms — all cyclic, so the index stays 1-dimensional

`N = #E(F_p)`, **not required prime**. `E(F_p) ≅ ℤ/N` required (asserted per curve, §5 C-CYC).
Characters are indexed by `a ∈ ℤ/N`; cells are the `(N−1)/6` `μ₆`-cosets on J0 (where `λ` acts) and
the `μ₂`-cosets `{±a}` elsewhere. `a = 0` excluded.

| arm | family | `Aut` | cofactor | selection rule (data-blind) |
|---|---|---|---|---|
| **J0** | `y² = x³ + B` | `μ₆` | **1** (`N` prime) | least 2 **distinct `F_p`-iso classes** with `N` prime |
| **J1728** | `y² = x³ + Ax` | `μ₄` | **2** | least 2 iso classes with `χ₂(−A) = −1`, `N = 2n'`, `n'` prime, cyclic |
| **JGEN-1** | `y² = x³+Ax+B`, `j ∉ {0,1728}` | `μ₂` | **1** | least 2 iso classes, `N` prime |
| **JGEN-2** | as above | `μ₂` | **2** | least 2 iso classes, `N = 2n'`, `n'` prime, cyclic |

**JGEN-1 vs JGEN-2 is the internal control for the unavoidable cofactor mismatch** (§1). If `g₃ = 0`
at both, cofactor does not drive the statistic and the J0(h=1) vs J1728(h=2) comparison is
interpretable. If they differ, the comparison is **void** and is reported as void.

**Iso classes, not parameter values** *(gate D6)*: `(x,y) ↦ (u²x, u³y)` sends `V ↦ χ₂(u)V`, i.e.
`L* ↦ L*(±T)`, leaving `g_k` invariant — so distinct `B` values in one twist class are duplicates,
not replicates. v1's "least B, then next 2" returned duplicates at 11 of 14 primes. Units are
**counted as distinct iso classes**, and the count is reported.

**Primes (FROZEN):** all `p ≡ 1 mod 3` with `30 < p < 250` (J0 requires `p ≡ 1 mod 3` to be
ordinary — gate D7; there is no J0 at `p ≡ 2 mod 3`). Both `p mod 4` classes are in scope; the
closure sign is handled by `e₃ = χ₂(−1)·p·e₁` and is asserted per prime.

**Character-order stratification** *(new)*: on cofactor-2 arms, every reported cell carries
`ord(a) ∈ {2, n', 2n'}` and results are reported **per order**. If the lock's presence depended on
character order, that would otherwise be invisible.

## 3. Statistic, and the certification direction

`g_k(p,A,B,a) = deg gcd(L*(T), L*(ζ_k T))`, `k ∈ {3,4,6}`, multi-modular over 5 primes
`l ≡ 1 mod (k·N)` **per k** *(gate D2: v1's code hardcoded `step = 3n`, so `4 | l−1` failed at 2–3
of 5 ells)*, with `ζ_k` of **exact** order `k` *(gate D1: the predecessor's `primitive_root_of_order`
returns order 3 for `k=6` at 3 of 5 ells, which computes `g₃` and reports it as `g₆`)*.

> **★ `min_l g_l ≥ g_true` — the bound is ONE-SIDED** *(gate D3; see
> `CORRECTION_120deg_census_certification_direction_v1.md`)*. A computed **0 certifies `g_true = 0`
> exactly**; a computed **2 certifies only `g_true ≤ 2`**. Witness: the predecessor's PLANT-B, true
> `g₃ = 0`, reads `deg gcd = 2` at `l = 13` and `l = 37`.

**Consequence for this spec, and it is favourable:** every prediction in §4 off `j=0` is **0**, which
is the exactly-certified direction. The one positive prediction (J1728 `g₄ = 2`) is on the
uncertified side and therefore **requires a characteristic-0 certificate**: `Res_T(L*, L*(ζ_kT)) = 0`
and first subresultant `= 0`, computed exactly in `ℤ[x]/(Φ_N(x), Φ_k(x))` via the core's
`polymul_mod_cyc` / `reduce_phi_prime`. Any cell reported `g_k ≥ 1` without a certificate is reported
as `g_k ≤ bound`, never as `g_k = value`. Per-cell spread `max_l g_l − min_l g_l` is printed always.

**Reachable values** *(gate D4)*: `g₃ ∈ {0,1,2}`; `g₄ ∈ {0,1,2,4}` with `4` only at `e₁=0` (censused);
`g₆ ∈ {0,1,2,3}` with `3` census-surviving. §4 gives a reading for each.

## 4. PRE-COMMITTED PREDICTIONS (decidable; counts, not adverbs — gate F1/F2)

| arm | `g₃` | `g₄` | `g₆` |
|---|---|---|---|
| **J0** (`μ₆`) | **2** at every surviving cell | **0** | **0** |
| **J1728** (`μ₄`) | **0** at every surviving cell | **2** at every surviving cell, certified | **0** |
| **JGEN-1/2** (`μ₂`) | **0** | **0** | **0** |

**★ J0 `g₆ = 0`, corrected from v1's `2`** *(gate P1, independently re-derived)*: on
`{α, ζ₃α, −ᾱ, −ζ̄₃ᾱ}` the ordered angle differences are `{±120, 180−2θ, 60−2θ, −60−2θ}`; `g₆ = 2`
needs a difference of `±60`, i.e. `θ ∈ {0, ±60}` — three isolated angles. Exhaustively, 2848 of 2864
distinct-root configs with `g₃ = 2` have `g₆ = 0`. **The correct near-corollary of `g₃=2` is `g₆=0`.**

**Decidable form of "every":** for each arm and each `k`, report `(#surviving cells, #cells attaining
the predicted value, list of every deviating cell as `(p, A, B, a, ord(a), g_k)` verbatim)`. A row
holds iff the deviation list is empty.

## 5. FALSIFICATION — exhaustive and mutually exclusive (gate F3)

Evaluated in order; the first that applies is the verdict.

- **F-VOID.** JGEN-1 and JGEN-2 disagree on any `g_k` row ⇒ the cofactor mismatch drives the
  statistic ⇒ **the J0/J1728 comparison is void.** Report as void; no mechanism conclusion.
- **F-A (mechanism REFUTED; the most interesting outcome available).** ≥ 1 surviving JGEN cell with
  distinct roots, `e₁ ≠ 0`, and a **char-0-certified** `g₃ = 2`. The `ζ₃` is then not an
  automorphism/CM phenomenon. **Report as a positive finding, not a failed prediction.**
- **F-B (REFUTED in its `μ₃`-specific form).** ≥ 1 certified `g₃ = 2` on J1728.
- **F-C (SURVIVES but is not `Aut`-shaped).** J1728 shows `g₃ = 0` **and** `g₄ = 0` at every
  surviving cell. The lock is `μ₃`-specific rather than "`Aut` acts"; the `W ⊗ R` reading predicts a
  lock and does not get one. Weakens the mechanism without refuting it.
- **F-D (necessary condition met).** The §4 table holds in full. Licenses §7 and nothing more.
- **F-E (unanticipated value).** Any surviving cell with `g₃ = 1`, `g₆ = 3`, or an off-arm lock not
  covered above ⇒ **no verdict**; the cell is reported verbatim and the spec is reissued. Recorded
  explicitly so that an unanticipated value routes to a re-spec rather than to a post-hoc gloss.
- **F-EMPTY.** Any arm with 0 curves or 0 surviving cells at ≥ half its primes ⇒ that arm reports
  **empty**, and every falsification clause depending on it is **unevaluable**, stated as such.
  *(v1 had no such clause and would have routed the dominant outcome into a deviations entry.)*

**Within-arm heterogeneity:** if the 2 iso classes of an arm disagree at any prime, the arm reports
**heterogeneous** and its row does not hold, regardless of majority.

## 6. Controls — all must fire before any arm number is read

| id | control | requirement | status |
|---|---|---|---|
| **C-ORDER** | `root_of_order(k,l)` exact order, `k ∈ {3,4,6,12}` | order == k asserted per `(k,l)` | **built, PASS** |
| **C-PLANT** | 3 positive + 1 **verified lock-free** negative + 6 cross-order, over `F_l` | all fire | **built, ALL FIRE** |
| **C-REPRO** | generalized pipeline vs `RESULT_n1_120deg_exact_v1.json` | cell-for-cell | **built, PASS at `p=43,67,79,127`** |
| **C-EXACT** | `check_no_float.py` | clean | **built, OK** |
| **C-CYC** | `E(F_p)` cyclic; a generator of order `N` exists | asserted per curve | to build |
| **C-COEFF** *(gate C1)* | the `V₂ → e₂` sign, on the **new** code path | independent `e₂` at ≥1 curve/arm at small `p` | **to build — load-bearing: a sign error reproduces the entire predicted table, since every off-`j=0` prediction is 0** |
| **C-FORCED** *(gate C2)* | `e₃ = χ₂(−1)p·e₁`, `e₄ = p²` are *definitions* here; unverified off `j=0` | independent eigenvalue check at ≥1 curve/arm | to build |
| **C-FIRE4** *(gate C3)* | **firing control for the positive prediction on curve-derived data** | real `e₁` from an arm cell + `e₂` solved exactly so the multiset is `{α,ζ₄α,−ᾱ,ζ₄ᾱ}`; pushed through the **full** downstream; must report `g₄ = 2` **and** survive the `V=0` census and repeated-root filter | to build |
| **C-ZERO** *(gate C4)* | `e₁=0` corners: `T⁴−pT²+p²` (`g₃=g₆=2`), `T⁴+p²` (`g₄=4`) | must be removed by the `V=0` census | to build |
| **C-NEG** *(gate C5)* | negative plants **pinned per `k`** as concrete instances, not a condition family | v4 ⟪GATE-5⟫ found 708 accidental `g=2` multisets under an unpinned rule | partly built (pinned, lock-free) |

**C-PLANT alone is insufficient** *(gate C3)*: it feeds synthetic quartics straight into `deg_gcd`,
exercising none of `V₁→V₂→e₂→e₃/e₄→L*→embedding→census→filter`. Without C-FIRE4, "`g₄ = 0` off
`j=0`" is indistinguishable from "the pipeline cannot emit `g₄ = 2` on curve-derived input."

**Registered code change** *(gate D9)*: `audit_n1_vsign_v2_core.py` has no `A` parameter at 8 sites,
including the two doubling slopes (`:50`, `:134`) which are silent failures. This spec runs
`jclass_120deg_discriminator_v1.py`, an **`A`-aware reimplementation**, not the core. C-REPRO passing
cell-for-cell at 4 primes is the evidence the port is faithful.

## 7. Scope — what a confirmed §4 table licenses

**Would:** *the `ζ₃` lock at `a≠0` is present on `μ₆` curves and absent on `μ₄` and `μ₂` curves, over
`p ≡ 1 mod 3`, `30 < p < 250`, at the stated iso-class and cell counts, with the `g=0` direction
exactly certified and the `g₄=2` direction certificate-backed* — `[EMPIRICAL — exact, scoped]`.

**Would NOT:** (i) anything about the decomposition `H¹ ≅ W ⊕ W⊗ξ` (§0.1 — no eigenvalue statistic
can); (ii) uniformity in `a` at secp's `p` (this is `p < 250`); (iii) any leakage or ECDLP
consequence; (iv) promotion of the mechanism above `[CONJECTURAL]`; (v) anything about secp's own
**cofactor-1, `p ≡ 7 mod 12`** setting beyond the J0 arm, since J1728 exists only at cofactor 2.

**Grading asymmetry, stated** *(gate F7)*: the `g=0` rows are exactly certified; the `g₄=2` row is
certificate-backed; they are **not** the same grade and are not reported as such.

## 8. Deviations

`PREREG_jclass_120deg_discriminator_v2_DEVIATIONS.md`, opened at freeze. Freeze = SHA-256 of this
file, printed by the runner and recorded in the RESULT.
