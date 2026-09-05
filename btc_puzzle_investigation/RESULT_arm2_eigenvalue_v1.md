# RESULT — Arm 2 (Sage): the "dim 2" hypothesis is REFUTED; χ₂(y) is dim-4 A_new, the ½ is CM cancellation (v1, 2026-07-24)

**Spec:** `PREREG_mu3_orthogonal_projection_v1.md` §2.6 (Arm 2, twisted eigenvalue multiset).
**Purpose:** test `RESULT_mu3_projection_v1.md`'s hypothesis "single-factor χ₂ sum → H¹ top-mass
**dimension 2**". **Outcome: refuted — and replaced by the correct structure.**
**Scripts (Sage 10.9):** `sage_arm2_eig_v2.sage` (twisted deg-4 config), `sage_arm2_cover_v2.sage`
(χ₂(x) cover), `sage_arm2_cy_v2.sage` / `sage_arm2_summary_v1.sage` (χ₂(y) = A_new). Exact zeta /
point counts; no float in the arithmetic.

---

## 1. The hypothesis was WRONG — χ₂(y) is dimension 4, not 2

`RESULT_mu3_projection_v1.md` §2 hypothesised that χ₂(y)'s attained `2√p` (½ of its `4√p` ceiling)
means the carrying `H¹` is 2-dimensional. **Sage's exact cover zeta functions refute this:**

| readout | cover `C_f : w²=f` | genus | new part `L_{C_f}/L_E` | eigenvalues | ceiling |
|---|---|---|---|---|---|
| **χ₂(x)** | `y²=w⁶+B` | 2 | **degree 2 (dim-1 AV)** | **2**, `\|α\|=√p` | `2√p` |
| **χ₂(y)** | `w⁴=x³+B` | 3 | **degree 4 (dim-2 AV = A_new)** | **4**, `\|α\|=√p` | `4√p` |

(exact, rem 0, primes 13/43/61/67/79/103/127/139 for χ₂(x); 13/43/61/67/79/103/127 for χ₂(y)).

> **χ₂(y) carries a genuinely 4-dimensional `H¹` (the abelian surface A_new).** The hypothesis "dim 2"
> is false. The ½ is **not** a dimension reduction.

**The two `2√p`'s have DIFFERENT causes** — which is why Experiment 1's self-null saw χ₂(x) and χ₂(y)
behave alike while they are structurally different:
- **χ₂(x) attains `2√p` because it only HAS 2 eigenvalues** (dim-1 new part). Dimensional.
- **χ₂(y) attains `2√p` despite having 4** eigenvalues (ceiling `4√p`). A cancellation.

---

## 2. The correct structure of A_new — exact, and it IS the addendum's m-law object

For the ordinary primes tested, `L_{C_y}/L_E = T⁴ + m·p·T² + p²` with **m = 1**
(p=43,67,79,103,127; p=13 and the anomalous p=61 differ). This is **even in `T`**, so the 4 Frobenius
eigenvalues form **two antipodal pairs `{α, −α, ᾱ, −ᾱ}`**, at arguments

```
±60°, ±120°   =   √p · { ζ₆, ζ₆⁻¹, ζ₃, ζ₃⁻¹ }     (primitive 6th and 3rd roots)
```

verified exact on p=43/67/79/103. **This is precisely the eigenvalue set
`POSITIVE_FINDINGS_ADDENDUM_1_v1.md` §A2.2 predicts for `m=1`** ("eigenvalues √p·{ω,ω²,ζ₆,ζ₆⁵}, root
orders [3,3,6,6]") — now exhibited directly at ordinary primes, with the CM structure pinned. The
untwisted trace of these four is `√p(2cos60° + 2cos120°) = 0`, consistent with the even char poly.

The **twisted** deg-4 config (base change over `F_{p^k}`, k≤4, at p=13) confirms 4 **pure** eigenvalues
(`|α|/√p = 1.000`) carrying the μ₃ signature — arguments `{±38°, ±158°}`, spacing `158−38 = 120°`.

---

## 3. What Arm 2 settled, and what it did not

**Settled (exact):**
- χ₂(x) new part = dim-1 AV (2 eigenvalues) ⇒ `|V_x| ≤ 2√p` is a **dimension** fact.
- χ₂(y) new part = **dim-2 A_new** (4 eigenvalues, even char poly `T⁴+mpT²+p²`, m=1, CM eigenvalues
  at ±60°/±120°) ⇒ ceiling `4√p`.
- ⇒ **the Experiment-1 "dim 2" hypothesis for χ₂(y) is REFUTED.** The ½ (attained `2√p` vs ceiling
  `4√p`, established exact on 22 primes in Experiment 1) is a **cancellation among 4 CM eigenvalues**,
  not a reduced dimension.

**NOT settled — the refined open problem:** an exact proof that the CM/parity structure caps the
*twisted* attained magnitude at exactly `2√p`. The even structure `{α,−α,ᾱ,−ᾱ}` plus the odd-under-[−1]
readout (M4: `V(−a)=χ₂(−1)V(a)`) is the natural candidate — the addendum §A2.6-4 "[−1] splits A_new
2+2, a definite-parity y-readout couples to one 2-dim half ⇒ ½". Arm 2 makes that candidate concrete
(the 2+2 = the two antipodal eigenvalue pairs) but does **not** prove the twisted cap. Grade
`[CANDIDATE]`.

---

## 4. Net effect on the N1 ledger

| claim | before Arm 2 | after Arm 2 |
|---|---|---|
| N1 ½ magnitude `= 2√p/4√p` | `[VERIFIED exact, 22 primes]` | unchanged — **stands** |
| "2 of 4 eigenvalues starved" | refuted (Exp 1) | refuted — **and now the 4 eigenvalues are exhibited** (±60/±120) |
| χ₂(y) → H¹ dim 2 | `[HYPOTHESIS]` (Exp 1) | **REFUTED — χ₂(y) is dim 4 (A_new)** |
| mechanism of the ½ | "single-factor cap" (vague) | **CM cancellation in dim-4 A_new**; exact cap `[CANDIDATE: [−1] 2+2 split]` |
| A_new = `T⁴+mpT²+p²`, m=1, eig ±60/±120 | asserted for secp `[CONDITIONAL]` | **exhibited exact at ordinary primes** (43…127) |

**Honest summary for the user's request** ("turn the dim-2 hypothesis into a proof"): Arm 2 did the
opposite and better — it **falsified** the dim-2 hypothesis with exact cover zeta functions, pinned the
true object (dim-4 A_new, even CM char poly, eigenvalues ±60/±120), and reduced the mechanism to one
sharp open statement (does the [−1]-parity 2+2 split cap the twisted trace at 2√p?). The N1 ½
*magnitude* remains resolved; its *mechanism* is now correctly located.

**No ECDLP content.** `p ≤ 139` (cover zeta) / `p = 13` (twisted config); pins Frobenius eigenvalues of
an abelian surface, approaches no scalar bit.

*Grade legend: VERIFIED (exact) · REFUTED · CANDIDATE · CONDITIONAL.*
