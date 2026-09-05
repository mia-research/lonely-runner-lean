# RESULT — H¹ structure of the χ₂-cover, supersingularity, and why `p ≡ 7 mod 12` matters

**Date 2026-07-19.** Object: `C : w⁴ = x³ + B`, the cover carrying the χ₂(y) readout (`w²=y`,
`y²=x³+B`). Scripts: `mu6_cohomology_split_v1..v4.py` (Sage, exact over GF(p)/QQ/cyclotomic),
plus the parity/DFT check. Matched non-CM control `w⁴=x³+2x+5` throughout.
**Anomaly-Drill protocol:** characterization only; every claim carries its scope; named mechanisms
are killed when the data kills them; failed predictions are stated, not buried.

---

## 0. THE HEADLINE: `p_secp ≡ 7 mod 12` — and that is *secp's own class*

`p = 2²⁵⁶ − 2³² − 977` ⇒ **`p ≡ 3 mod 4`, `p ≡ 1 mod 3`, hence `p ≡ 7 mod 12`** `[VERIFIED exact]`.
This is why the congruence matters: `7 mod 12` is exactly the **conjunction** of the two independent
structures below — `3 mod 4` (exact vanishing + supersingular cover) and `1 mod 3` (ζ₃ ∈ F_p, so the
μ₃/CM automorphism is defined). Both of secp's relevant features sit in that one class.
*(For contrast: `n ≡ 1 mod 4`, `n ≡ 1 mod 3`.)*

## 1. THREE SEPARATE LAWS, THREE SEPARATE SCOPES

**L1 — an EXACT conservation `[PROVED, elementary; curve-independent; scale-free]`.**
`p ≡ 3 mod 4 ⇒ χ₂(−1) = −1 ⇒ χ₂(y_{−P}) = χ₂(−y_P) = −χ₂(y_P)`. The involution `[−1]` pairs `P` with
`−P`; 2-torsion contributes `χ₂(0)=0`. Hence
> **`Σ_{P∈E(F_p)} χ₂(y_P) = 0` exactly, for every elliptic curve, whenever `p ≡ 3 mod 4`.**

`[VERIFIED 12/12]` (6 CM + 6 non-CM primes ≡3 mod 4). **Applies to secp** (theorem, no scale limit).
**The converse is FALSE:** non-CM `p=97` (≡1 mod 4, ordinary) has `Σχ₂(y_P)=0` **accidentally**. So L1
is an implication, not an equivalence — stated as ⟺ in the pre-registration and corrected here.

**L2 — the GEOMETRIC layer `[PROVED from automorphisms; VERIFIED 24/24]`.**
`ζ₄:(x,w)↦(x,iw) ∈ Aut(C)` for **any** cubic; `ζ₄² = (w↦−w)`; `E = C/⟨ζ₄²⟩`. So
`H¹(C) = H¹(E) ⊕ H¹_new` with `dim 2 + 4` (`L_E | L_C` exactly at every prime tested), and `ζ₄` acts
as `±i` on `H¹_new` — the **2+2 splitting** — giving `Q(i) ⊆ End⁰(A_new)`. Consequence:
> **`A_new` is supersingular ⟺ `p` inert in `Q(i)` ⟺ `p ≡ 3 mod 4`.** `[VERIFIED 24/24, both covers]`

This is **curve-independent** — that is its correct *scope*, not a defect. **Applies to secp**:
`A_new` is supersingular at `p_secp`.

**L3 — the CM layer `[PROVED from automorphisms; NO numerical discriminator found]`.**
Only when the cubic is `x³+B` (⟺ `j(E)=0`) does `ζ₃:(x,w)↦(ωx,w)` also act, giving `μ₁₂ ⊆ Aut(C)` and
`Q(ζ₁₂) ⊆ End⁰(A_new)`. Since `[Q(ζ₁₂):Q] = 4 = 2·dim(A_new)`, **`A_new` is a CM abelian surface**.
Applies to secp (`p≡1 mod 3` ⇒ ζ₃ ∈ F_p). Numerics are *consistent* (CM `L_new` splits over `Q(ζ₁₂)`
at **6/6** ordinary primes) but **do not establish it** — see §2.

## 2. FAILED PREDICTIONS AND RETRACTIONS (mine — stated plainly)

| claim | status |
|---|---|
| v1: "`p≡7 mod 12 ⇒ √p·ζ₆`, a CM fingerprint" | **FALSE.** CM `p=19` gives `ζ₂` (±√19); non-CM `p=43,79,103` give `ζ₆`. Retracted. |
| "`√−3` in the splitting field" = CM detector | **FALSE.** Non-CM shows `√−3` at `p=37,43,61,73,79`. |
| P-B: "`L_new` splits over `Q(ζ₁₂)`" = discriminator | **Uninformative — bad test design.** If the roots already lie in `Q(i) ⊂ Q(ζ₁₂)` it passes *trivially*. Non-CM passed **5/6**. |
| P-B′: "non-CM splits over `Q(i)`" | **FALSE, and the reasoning was wrong.** `Q(i)` has degree 2 acting on a **dim-2** `A_new` — degree 2, not `2·dim=4`, so it is **not CM** and `π` need not lie in `Q(i)`. Observed **2/6** (CM 1/6). No separation. |
| "χ₂(y) sits below its 4√p bound ⇒ y-parity / a 2+2 halving" | **REFUTED.** The parity is real (exact, every row) but `max|V|/√p` **does not split by `p mod 4`**: even-parity `1.73,1.91,1.84,2.00,2.00` vs odd-parity `1.82,1.91,1.99` — same band. Moreover χ₂(x) (dim 2, ceiling 2√p) and χ₂(y) (dim 4, ceiling 4√p) **both** measure ≈2.0, so the ≈2 is a property of the max-over-frequencies statistic, not a hidden symmetry. My "extra structure" flag was an overread. |

> **Net: no numerical discriminator for the CM layer was found; two designed tests failed. L3 rests on
> the automorphism proof alone.** The numerics neither confirm nor refute it — they are consistent and
> non-discriminating, and that is the honest status.

**Observation, not a law** `[6 supersingular primes per curve]`: the order of `α²/p` at supersingular
primes is `{1,3}` for CM and `{3,4}` for non-CM — order 4 (`α²/p=i`) seen only for non-CM, order 1
(`α=±√p`) only for CM, order 3 shared. Sample too small to call a law; recorded as an open pattern.

## 3. DOES THE SUPERSINGULARITY TRANSFER TO `E`'s DLP? — three routes, each CHECKED

*(An earlier draft asserted "no MOV/pairing transfer follows" and called `A_new` "auxiliary". That was
a **declaration**, not an analysis — and a careless one, since **cover-based DLP transfer (GHS / Weil
descent) is a real attack family** and `C→E` is exactly a cover. Replaced with decidable checks.
Route 3 remains genuinely open at the algorithmic level.)*

**Route 1 — MOV/pairing on `E` directly.** `[VERIFIED computationally]`
`ord_n(p) = (n−1)/6` **exactly**, bit-length **254**
(`=19298681539552699237261830834781317975472927379845817397100860523586360249056`). Also
`a_p = t = 432420386565659656852420866390673177327` with `0<t<p` ⇒ `t ≢ 0 mod p` ⇒ **`E` is ORDINARY**.
MOV needs a *small* embedding degree; `2²⁵⁴` is not small. **Blocked — verified here, not cited.**

**Route 2 — push `E`'s DLP into the supersingular `A_new` to borrow its pairing-friendliness.**
`[VERIFIED 18/18]` This requires `Hom(E, A_new) ≠ 0`. By **Tate's isogeny theorem** that holds iff `E`
and `A_new` share an isogeny factor iff `L_E`, `L_new` share a root. Measured:
> **`gcd(L_E, L_new) = 1` at every tested prime, both covers (18/18).**

Structurally identical conclusion: at `p ≡ 3 mod 4`, `E` is ordinary (Newton slopes `{0,1}`) while
`A_new` is supersingular (slope `½`) — disjoint slopes ⇒ no nonzero homomorphisms. **The DLP cannot
enter `A_new`; its small embedding degree is unreachable from `E`. Blocked — verified.**

**Route 3 — cover transfer into `Jac(C)` (genus 3) via `C→E`.** `[CITED — OPEN algorithmically]`
This transfer **does exist**: the degree-2 cover embeds `E` into `Jac(C)` up to isogeny, so a DLP
instance in `E(F_p)` genuinely moves into `Jac(C)(F_p)`. Does it help? Index calculus on genus `g` over
`F_q` costs `Õ(q^{2−2/g})` **[CITED — Diem]**; `g=3` ⇒ `Õ(p^{4/3})` against `O(p^{1/2})` for Pollard on
`E` — worse by `p^{5/6}`. And `Jac(C) ~ E × A_new` with `Hom(E,A_new)=0`, so the transfer carries the
DLP into the `E`-component while `A_new` receives nothing: `E`'s problem plus dead weight.
*(GHS/Weil descent proper needs an extension field `F_{q^n}`, `n>1`; secp is over a prime field.)*
> **HONEST STATUS: no advantage from the best KNOWN genus-3 algorithms. That is NOT a proof that no
> better genus-3 algorithm exists, and it covers exactly ONE cover (`w⁴=x³+B`). The family of covers of
> `E` is large; a cover with a better genus/field trade-off is NOT excluded. Route 3 stays OPEN.**

**What the supersingularity does mean:** at `p_secp` the χ₂(y) *untwisted* readout vanishes identically
(L1, proved at full scale) and `A_new`'s eigenvalues are `√p ×` roots of unity (maximal rigidity),
pinning the `a=0` mode exactly. It does not improve `|V(a)| ≤ 4√p` for `a≠0`.

## 3b. RETRACTION OF A DISMISSAL — the χ₂(y) sub-bound is REAL `[VERIFIED]`

An earlier pass killed the χ₂(y) sub-bound with two bad arguments, **both refuted by measurement**
(`chi2y_saturation_v1.py`). Saturation = (measured max) / (its own ceiling `dim·√p`):

| readout | dim H¹_c | ceiling | saturation (mean, range) |
|---|---|---|---|
| additive `bx+cy` | **4** | 4√p | **0.876** [0.807–0.917] |
| additive `bx` | 3 | 3√p | 0.909 [0.809–0.964] |
| χ₂(x) | 2 | 2√p | 0.947 [0.822–0.998] |
| **χ₂(y)** | **4** | **4√p** | **0.470** [0.432–0.500] |

- **Decisive control:** additive `bx+cy` has the **same dim 4, same ceiling, same frequency count, same
  estimator** — yet saturates `0.876` vs χ₂(y)'s `0.470`. A **1.86× systematic gap at identical
  dimension**, which a max-over-frequencies artifact **cannot** produce. My earlier
  "both ≈2.0 ⇒ artifact" argument compared RAW values and erased the normalized object: **withdrawn.**
- χ₂(y) converges to **exactly ½** (0.432, 0.455, 0.477, 0.459, 0.500, 0.499) ⇒ effectively only
  **2 of 4** eigenvalues carry weight-1 mass at the maximizing frequency — the **2+2 splitting**
  originally proposed and wrongly killed. **Live, named, OPEN.**
- **Parity, corrected:** the phase test confirms it exactly — `V(a)` is purely **real** at every
  `p≡1 mod 4`, purely **imaginary** at every `p≡3 mod 4`, every row. My earlier "parity refuted" test
  aimed a **magnitude** statistic at a **phase** constraint, on 3-vs-5 unmatched primes confounded by a
  strong `n`-trend — an uninformative null. **But** parity does not *cause* the ½ (both classes ≈0.47).
  **Two distinct real structures; the ½ mechanism is unidentified and open.**

## 4. What is genuinely open (named, not closed)

1. **A discriminating numerical signature for L3 (the CM layer).** Field-splitting tests fail (§2). A
   real test would target the **CM type** (the specific embedding of `Q(ζ₁₂)` acting on the tangent
   space), not which field `L_new` splits over.
2. **The supersingular order sets `{1,3}` vs `{3,4}`** — larger sample needed before it is a law.
3. **The `a≠0` twisted modes.** L1 pins only `a=0`. The cohomological ceiling `4√p` stands
   (`weil_deligne_character_bound_v1.md`); the observed ≈2√p is the generic max-of-character-sum
   scale, not structure.
