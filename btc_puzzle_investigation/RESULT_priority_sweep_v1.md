# RESULT — priority / literature sweep of the 10 "undocumented elsewhere" claims

*2026-07-24. Executes `PREREG_priority_sweep_v1.md` (frozen pre-search). Positive-control gate:
**PASSED** — all three known-published controls recovered before any claim was searched. Product is a
**citation map**, not a novelty verdict; the strongest statement made is "no prior located under the
frozen protocol." Deviations: `PREREG_priority_sweep_v1_DEVIATIONS.md`.*

**No leakage / ECDLP claim. This is a literature audit of `NEXT_DIRECTIONS_v1.md §2`.**

---

## 0. Gate (must pass, or the sweep is void)

| control | recovered? | citation |
|---|---|---|
| PC-1 Silverman–Stange amicable pairs | **yes** | Exp. Math. 20(3) 2011, 329–357; [arXiv:0912.1831](https://arxiv.org/abs/0912.1831) |
| PC-2 Kohel–Shparlinski exp. sums | **yes** | ANTS-IV 2000, LNCS 1838, 395–404 |
| PC-3 Waterhouse ab. var. / finite fields | **yes** | Ann. Sci. ÉNS 1969, 521–560 (NUMDAM) |

**Gate PASSED.** The instrument finds published results across both literatures (EC arithmetic +
character sums + class field theory), so a "no prior located" verdict is informative.

## 1. The headline

> **Not one of the 10 is a novel theorem.** Every one reduces to classical or established machinery;
> the record's contribution in each case is an **application / instance / re-derivation**, not a new
> result. This is the same pattern the record already logged five times ("reading the source
> dissolved the obstacle") — now confirmed **systematically across all 10.**

⚠ **Honest accounting of what the SEARCH added vs. what was pre-known.** For **5 of the 10 the verdict
was known before any query** and the search was confirmatory (bookkeeping value, not discovery):
**#8** Parseval (proved *this session*), **#6-framework** (the record's own text says it is published),
**#1, #2, #10** (textbook). The prereg's pre-commitment of #6/#8 to FOUND "by construction" is the tell.
The search added **genuine, previously-unknown information for 5**: **#3** (Berndt–Evans 1977 — the one
actionable find), **#5, #7, #9** (the specific papers, not just that such literatures exist), and
**#6-instance** (secp not previously located as amicable). **This item was ranked #1 as "highest
value"; that overstated it — half the list was pre-known, and the one nugget (#3) was reachable
directly. Recorded so the sweep is not read as an investigation of 10 open questions.**

The only genuinely **no-prior-located** residue is **narrow and specific**: that **secp256k1
specifically** is an amicable pair (claim 6 instance), and a handful of exact *identifications* the
record makes on top of classical objects (`m` = a specific Jacobi sign, `|FLD| = 6h(−p)` with the
constant 6). These are applications of published machinery, not theorems missing from the literature.

## 2. Per-claim citation map (frozen 3-grade rule: FOUND / PARTIAL / NO-PRIOR-LOCATED)

| # | claim | grade | prior located / delta |
|---|---|---|---|
| 1 | Cap Law / flap = exact `ℤ[ω]` lattice region | **FOUND (concept)** | Eisenstein-integer division by rounding to the nearest lattice point, the 60°–120° rhombus fundamental domain and its **Voronoi region**, are standard lattice / coding-theory objects ([arXiv:1404.1312](https://arxiv.org/pdf/1404.1312), ETRU, HandWiki). The "carry region" is the complement of the nearest-point cell. Delta: the record's `|u∓v|>½` phrasing. |
| 2 | `H1`: `(−1)^{flap/6} = χ₂(2)` via a lattice count | **FOUND (concept)** | The **second supplement** `(2/p)=(−1)^{(p²−1)/8}` has classical **lattice-point / Gauss-lemma proofs** (Eisenstein 1844). `ORB = |T⁺|/3` is a rephrasing of a lattice-count Legendre-symbol argument. |
| 3 | `\|FLD\| = 6·h(−p)` | **PARTIAL** | **The class number as a finite Dedekind-sum is classical: Berndt–Evans 1977, Goldstein–Razar 1976** (`h_K = (w²/4)Σχ_K(n)s(n,D)`; `p≡3 mod4 ⇒ h² = 2S(H₂,p)`). The record's `(†)` uses the **sawtooth `sgn(ρs mod p−s)`**, the Fourier-dual of the cotangent Dedekind sum. Delta: the exact constant 6 and the `FLD` set. **→ ACTIONABLE (§4).** |
| 4 | Claim S / Claim F (isotypic selection; FIELD+CURVE split) | **PARTIAL (concept)** | Point counts of `j=0` sextic-twist curves `y²=x³+d` via **Gauss / Jacobi sums** and the μ₆ sextic-residue character are classical (Ireland–Rosen ch. 8). Delta: the record's organization ("one rule absorbs five zeros"; the mandatory split). |
| 5 | `A_new` (`w⁴=x³+b`) supersingular ∀`p≡3 mod4`, μ₄ not CM | **PARTIAL** | Supersingular **cyclic / superelliptic covers** are a studied family: Moonen's classification, Li–Mantovan–Pries–Tang, Streng "Explicit supersingular cyclic curves" ([arXiv:2501.14902](https://arxiv.org/abs/2501.14902)). Delta: the explicit `w⁴=x³+b` + `p≡3 mod4` criterion as a *named* statement not located; very likely a special case (Newton polygon of a μ₄ cover). |
| 6 | secp256k1 **is** an amicable pair | **framework FOUND / instance NO-PRIOR-LOCATED** | Framework = PC-1 (Silverman–Stange), incl. their theorem *CM `j≠0` ⇒ no cycles > 2* — which is exactly why secp's `j=0` is the open case. **No paper stating secp specifically is an amicable pair was located** (bounded; a finite computation apparently unpublished). |
| 7 | char poly `t⁴+mpt²+p²`, `m` names the eigenvalues | **PARTIAL** | The **supersingular abelian-surface char-poly form `t⁴+a₁t³+a₂t²+qa₁t+q²`** and its classification by `(a₁,a₂)` are established (Singh–McGuire, [arXiv:1011.2257](https://arxiv.org/abs/1011.2257), [1110.1116](https://arxiv.org/pdf/1110.1116)). With `a₁=0`: `t⁴+mp t²+p²`. Delta: `m` = a single **Jacobi-sum sign** (the record's, and the open Jacobi-sign law). |
| 8 | three exact `U`-conservations, headline `Σ_a\|U\|²=n(n−1)` | **FOUND** | Headline = **Parseval/Plancherel** on the finite abelian group `ℤ/n` (Keith Conrad; standard). Confirmed this session to hold for **any** unit-modulus target — not curve-special. The other two conservations are also standard Fourier identities. |
| 9 | bilinear closure (`\|S\|/n² = O(p^{−1/2})`) | **PARTIAL / FOUND** | **Bilinear exponential sums over EC points with `√p`-type bounds are established:** Ahmadi–Shparlinski "Bilinear character sums…on elliptic curves"; "Exponential sums over points of elliptic curves" (JNT 2014); Bombieri gives `O(√p)` for single-variable function-field sums. Delta: the record's specific two-point Fourier factorization as a technique. |
| 10 | `k_den` level sets = primitive Farey comb | **FOUND** | Classical **Farey / Stern–Brocot** structure: level `n` adds exactly the `φ(n)` irreducibles of denominator `n`; `L_n = 1+Σφ(k)`. A restatement of standard Farey theory. |

**Tally (frozen denominator = 10):** FOUND 4 (#1,2,8,10) + FOUND-framework 1 (#6-fw); PARTIAL 5
(#3,4,5,7,9); NO-PRIOR-LOCATED 1 (#6-instance). **Zero claims graded a novel theorem.**

## 3. Coverage ledger (the power number)

~3 frozen query variants per claim executed via `WebSearch` (which aggregates Google Scholar / arXiv
/ Semantic Scholar / Crossref in one query) plus targeted `WebFetch` on decisive hits, plus on-disk
grep for PC-2. **Deviation from the spec's D1–D4 as *separate* databases:** `WebSearch` returns an
aggregate, so per-database hit counts were not separable; MathSciNet (D4) was not directly accessed
(the spec's Semantic-Scholar+Crossref substitute applied). Recorded in the deviations file; it lowers
the confidence of the NO-PRIOR-LOCATED verdicts (which is why they are stated as *bounded searches*).

## 4. The actionable spin-off — claim 3 hands the `(†)` proof its tool

The earlier open item **`(†) C′−C = Σχ₂(s)·sgn(ρs mod p−s) = 3h(−p)`** (`NEXT_DIRECTIONS_v1.md §4`,
the single open step of P2 for `|FLD|=6h(−p)`) has a named classical home: **Berndt–Evans 1977 /
Goldstein–Razar 1976**, class number = finite Dedekind-sum. The sawtooth `sgn(ρs mod p−s)` is the
Fourier-dual of the cotangent Dedekind sum (cotangent = DFT of sawtooth). **So `(†)` is very likely
provable by rewriting the sign-sum as a Dedekind sum and applying the Berndt–Evans formula** — the
"source-first" move this project's methodology mandates, now with the source named.

## 5. What this does and does not establish

- **Establishes:** a citation map; that the record's originality claims are applications of classical
  machinery, not new theorems; and a named tool for `(†)`.
- **Does NOT establish:** that any claim is "novel" — every NO-PRIOR-LOCATED is a *bounded search*
  (§3 coverage caveat), and the one instance (secp amicable) may simply be an uncomputed folklore
  fact. Nor does it re-open item 2's genuine gap (the `2√p` cap), which is **not** in this list of 10
  and remains the one research-grade open problem.
- **Consequence for any writeup:** the marketable content is the **specific secp application** (secp
  is an amicable pair; the `m`/Jacobi and `|FLD|=6h` identifications), framed as *worked instances of
  classical theory*, never as new theorems. Framing them as novel would not survive review.
