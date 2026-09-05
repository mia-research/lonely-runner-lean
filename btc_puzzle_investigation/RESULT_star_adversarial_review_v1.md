# RESULT — defect A2 discharged: the reduction (★) survives an independent adversarial pass

*2026-07-30. Discharges **A2** of `RESULT_jacobi_closed_form_m_law_v4.md`'s self-audit (*"`[PROVED]`
applied without adversarial review … The reduction (★) has had **none**"*), the standing requirement of
CLAUDE.md §3/§7. Reviewer: isolated `general-purpose` subagent, given the statement of (★), (F1), (F2)
and three named file regions only — no session narrative, no summary/handover/master document, no memory
directory, and no statement of which conclusion was wanted. Instructed explicitly that it was **not
scored on problems found** and that a clean result stated plainly was a valid outcome. Exact arithmetic
mandated. No leakage or ECDLP claim.*

---

## 1. Verdict

> **(★) `S = χ₃(B)·J(χ₃,χ₄) + χ̄₃(B)·J(χ̄₃,χ₄)` is CORRECT.** Re-derived from scratch by the reviewer,
> independently of the project's derivation, and confirmed exactly at **598 `(p,B)` pairs with zero
> failures** (528 in-sample = all 12 primes `p ≡ 3 mod 4` under 100 × **all** `B ∈ F_p^*`; 70
> out-of-sample over 15 primes `101 < p < 250`). **A2 is discharged.**

The reviewer's convention (`χ(0)=0`; `J(χ,λ) = Σ_t χ(t)λ(1−t)`, Ireland–Rosen / BEW) matches the file's
use. Two things the file is silent on are **not** gaps under that convention: the `u=0` fibre (the count
`1 + χ₃(u) + χ̄₃(u)` is already correct at `u=0`) and the `x³+B=0` terms (killed by `χ₄(0)=0` in all three
sums at once). `χ₃(−1)=1` follows from `χ₃(−1)²=χ₃(−1)³=1`.

**(F1) and (F2) are both correct and correctly applied.** (F1) is load-bearing, not decorative: dropping
`B ∈ F_p^*` breaks (★) on a majority of `B ∈ F_q^*\F_p^*` (396 of 494 sampled at `p=7,11,19`), and the
correct general form is `S = χ₄(B)·[…]`. `3 | q−1` holds in both classes (`3|p−1` at `p≡1 mod3`,
`3|p+1` at `p≡2 mod3`). `p=3` needs no exclusion: `|F_9^*|=8` admits no order-3 character, so (★) is
vacuous there rather than false.

---

## 2. The one gap it raised — and why it resolves outside the fence

**Finding 7 `[B — gap]`:** the step `m = Re(S)/p`. The reviewer noted that in the three files it was
given, `A_new` is **never defined** and no identity links `S` to `b₂`; it named two needed items,
(a) `b₁ = 0` and (b) the lemma `b₂(A_new) = S`.

**This is a documentation gap in those three files, not a gap in the project.** Both items exist, in files
the fence excluded by design:

| item | where | status |
|---|---|---|
| `A_new` defined | `RESULT_mu4_eigenvalue_individual_v1.md:6`, `RESULT_mu6_cohomology_supersingular_v2.md:4`, `POSITIVE_FINDINGS_ADDENDUM_1_v1.md:64` | *"`A_new` = new part of `Jac(C)`, `C : w⁴ = f(x)`, `f` any separable cubic; `Jac(C) ~ E × A_new`, `dim A_new = 2`"* |
| `b₁ = 0` | `RESULT_anew_isogeny_type_correction_v1.md:32` | **FORCED — §A1.1 Fact 1 *derives* it** from the proved conjugation relation `π ζ₄ π⁻¹ = ζ₄⁻¹` (`RESULT_mu6_cover_and_conductor_v1.md:31`). Not asserted. |

**The reviewer independently reconstructed that same surface and verified the missing lemma.** Not having
been told the definition, it proposed `C : y⁴ = x³+B` (genus 3) with `A` = the `χ₄`-isotypic factor of
`Jac(C)` — the `j=1,3` pieces of `H¹`, interchanged by `Frob_p` since `χ₄^p=χ̄₄`, i.e. the complement of
the `j=2` piece `E : y²=x³+B` — and checked the point-count dictionary exactly:

```
#C(F_p) = p + 1 − a_p
#C(F_q) = q + 1 − a_p² + 2p + 2S          ⇒  b₂ = S,  m = S/p
```

**58/58 exact agreements**, `p ∈ {7,…,83}` × `B ∈ {1,2,3,7,11}`, both identities per pair, zero failures.
`b₁=0` is essential to the conversion (`Σβᵢ² = b₁² − 2b₂`, so `b₂ = −½Σβᵢ²` only when `b₁=0`) — and it is
the item §A1.1 derives.

> **Residual, small and named:** the reviewer verified the dictionary for **its own** reconstruction. One
> line is still owed tying the `χ₄`-isotypic factor of `Jac(w⁴=f)` to *"the new part complementary to
> `E`"* as the project defines `A_new`. The two descriptions coincide, but that coincidence is stated
> here, not proved. **This is the only item this pass leaves open on the `S→m` step.**

---

## 3. Three constructive results the pass produced

**3a. `[NEW — corrects the tally again]` `Im(S)=0` is algebraically forced, and is not on the A1
forced-list.** `x ↦ x^p` is a bijection and `B ∈ F_p`, so at `p ≡ 3 mod 4`
`S = Σχ₄((x³+B)^p) = Σχ₄^p(x³+B) = Σχ̄₄(x³+B) = conj(S)`, hence `S ∈ ℤ[i]∩ℝ = ℤ`. So §3's bullet *"`S` is
an exact rational integer in every case"* carries **zero** confirmatory information. A1 corrected the
tally from 34 to 15 distinct; this removes a further agreement from the evidence column. Per drill rule
(count only unforced hits) the forced-list in A1 should be extended.

**3b. `[NEW]` The single-`J` column is derivable — v4 records it as underived.** `RESULT_jacobi_closed_form_m_law_v4.md`
line 48 calls `J(χ̄₃,χ₄) = J(χ₃,χ₄)` *"observed numerically but **not derived**."* It follows from 3a: at
`p ≡ 7 mod 12` with `B` a cubic non-residue, `S = ωJ₁ + ω̄J₂` with `J₁,J₂ ∈ ℤ`, so
`Im S = (√3/2)(J₁−J₂) = 0 ⇒ J₁ = J₂`. Confirmed at 27 primes. ⇒ the `Re(·)` in `m = Re(S)/p` is redundant.

**3c. A3 (the norm-lift step) is NOT load-bearing for (★) or for the `m` table.** Nontriviality of
`χ₃|_{F_p^*}` plus `χ₃³=1` already forces the restriction to be one of the two cubic-residue characters,
and both enter `S` identically. A3 **is** load-bearing for the *sign law* (`RESULT_jacobi_sign_law_v1.md`
§2 steps (b),(e),(f)), and the pass confirms it is proved correctly there: the Frobenius-invariant
characters of `F_q^*` are exactly those trivial on `ker N`, which is the group of `(p−1)`-th powers, hence
exactly the norm-lifts. Step (e) needs the order-6 condition as well as the restriction, and the file
supplies it. *(So the earlier framing of A3 as a live blocker on `m` was mis-aimed — it never gated `m`.)*

**Also, independently re-derived (already on the ledger, not new):** the `G(χ₄)` sign rule
`g(χ₄) = (−1)^{(p+1)/4}p` is a theorem for every `p ≡ 3 mod 4`, not a 3-point fit — matching
`OPEN_ITEMS_LEDGER_v1.md` frontier 15's *"★ Sub-item DONE … bar lifted, it was never a fit."* Verified
14/14. The reviewer routes it through BEW 11.6.3 (`s=1`, needs only `N | p+1`); that citation is **not**
verified and no grade here rests on it, since the ledger already discharged the item via (S).

---

## 4. Scope of this pass — what it did NOT cover

- **The `J`-sign law itself was outside the fence.** The reviewer was given `RESULT_jacobi_sign_law_v1.md`
  (the 2026-07-25 file, which reports the `p≡1 mod 3` sign as open) and **not**
  `RESULT_jacobi_sign_law_stickelberger_v1.md`, which proves both halves. Its finding 10 therefore reports
  that sign as "still open"; **that is an artifact of the fence and is superseded** — do not cite it as a
  live gap. The fence was deliberate: the point was to audit (★) without the downstream framing.
- **(D2)/Katre is untouched** by this pass. `m=1` still carries the three Katre caveats, of which
  caveat 1 is load-bearing (the *printed* hypothesis `jk(j+k)≢0 mod m` is violated by `(4,3,12)`; only the
  proof's weaker `j,k,j+k ≢ 0 mod m` applies).
- **No `a≠0` content.** Nothing here bears on the uniformity gap of the 120° law, which is over
  `a ∈ (ℤ/n)*`; this is all the `a=0` anchor. See `RESULT_120deg_anchor_from_mlaw_v1.md` §5.
- **Novelty still doubted, not claimed** — unchanged from the predecessor's §6.

---

## 5. Ledger effect

| item | before | after |
|---|---|---|
| **A2** — (★) unreviewed | `[PROVED — UNREVIEWED]`, §3/§7 pass owed | **DISCHARGED** — independent pass, (★) `[PROVED]`, 598 pairs, 0 failures |
| **A3** — norm-lift | proved (`sign_law_v1` §2b); role unclear | **proved, and shown not to gate `m` at all** (§3c) |
| `J(χ̄₃,χ₄)=J(χ₃,χ₄)` | *"observed numerically, not derived"* | **derived** (§3b) |
| `Im(S)=0` as evidence | counted as agreement | **forced — removed from the evidence column** (§3a) |
| `A_new` / `b₂=S` / `b₁=0` | not stated in the m-law files | `A_new` and `b₁=0` located and derived elsewhere; dictionary verified 58/58; **one line owed** (§2 residual) |
| **`m=1` at secp** | `[PROVED — modulo (D2)] + UNREVIEWED reduction` | **`[PROVED — modulo (D2), 3 Katre caveats; + one line owed on the `A_new` identification]`** |

**On "unconditional".** The chain is now: `b₁=0` derived → `A_new` defined, `b₂=S` verified 58/58 (one
line owed) → (★) adversarially reviewed → `J`-sign law proved → (D2) cited-verified with caveat 1 → `7` a
cubic non-residue (exact). Every link is established or named. It is **not** unconditional while caveat 1
stands, because that caveat turns on citing a source's *proof* hypothesis against its *printed* one —
a judgment about a text, not a computation. Two items close it: a second source for (D2) stating the
digit-sum form for composite `m` and `f=2`, and the one-line `A_new` identification.
