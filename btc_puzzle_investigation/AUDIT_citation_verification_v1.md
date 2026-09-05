# AUDIT — citation verification of the bridge programme's classical inputs

**Date:** 2026-07-24 · Run by `citation-verifier` (CLAUDE.md §2 mandatory gate: a grade resting on a
citation). **Every load-bearing finding below was re-verified by me independently** before being acted
on (script: `scratchpad/` ad-hoc checks; results quoted inline). Trust-but-verify per CLAUDE.md §2.

**Net: 3 SUPPORTS, 2 SUPPORTS-WITH-CAVEAT, 1 CONTRADICTS, 1 NOT-FOUND-with-close-prior-art.**
Two corrections to the record and one **upgrade** follow.

---

## 1. CORRECTION — the ω-supplement's citation was wrong (the mathematics was not)

`RESULT_cubic_sextic_bridge_v1.md` (B2) cited **"Ireland–Rosen Prop 9.3.3"** for
`χ_λ(ω) = ω^{(a+b+1)/3}`. **IR Prop 9.3.3 is the solvability/multiplicativity proposition** — it says
nothing about `ω`. The supplement lives in **IR Ch. 9 Exercises (2nd ed., p. 135)**, and is stated as
eq. (1.1) of **Z.-H. Sun, *On the theory of cubic residues and nonresidues*, Acta Arith. 84 (1998), 291**
(which cites IR pp. 135, 313).

- **Formula: correct.** **Convention: correct** — our `a ≡ 2, b ≡ 0 (mod 3)` is the normalization that
  goes with this form. (Wikipedia's `a ≡ 1 mod 3` variant `ω^{(1−a−b)/3}` is the same law under
  `α ↦ −α`.)
- **UPGRADE.** The supplement is an **identity**, not an empirical fit:
  `(N(λ)−1)/3 ≡ (a+b+1)/3 (mod 3)` for primary `λ`. **I verified: 3659/3659** primary pairs
  `|a|,|b| ≤ 90`, 0 mismatches. Since `χ_λ(ω) = ω^{(N−1)/3}` holds by definition, **(B2) is provable,
  not merely `6000/6000`**.

> **Regrade (B2):** `[VERIFIED — classical, Ireland–Rosen Prop 9.3.3]` →
> **`[PROVED — identity (N(λ)−1)/3 ≡ (a+b+1)/3 mod 3; classical: IR 2nd ed. Ch. 9 Exercises p. 135;
> stated as eq. (1.1) in Sun, Acta Arith. 84 (1998) 291. NOT Prop 9.3.3.]`**

## 2. CORRECTION — (D1)'s "2 inert in the CM **field**" is wrong, and its direction was overstated

Two separate defects, both confirmed by me:

**(a) Field vs. order.** For non-maximal orders the gloss fails. `D = −12` (conductor 2): **2 is inert
in `K = ℚ(√−3)`**, yet `D ≡ 4 mod 8` and **every** order is even — I verified **6028/6028 even**. The
condition is on the **order `O_D`**, not the field.

**(b) Direction.** `D ≡ 5 mod 8 ⇒ odd order` is **FALSE pointwise**. `p = 7`, `D = −3 ≡ 5 mod 8`:
`y²=x³+k` over `F₇` has orders **{3,4,7,9,12,13}** — four of them even. (`F₁₃`: {7,9,12,16,19,21}.)
Only the converse is a theorem:

> **Bröker–Stevenhagen, *Constructing elliptic curves of prime order*, §2:** for `π ∈ O_D` of prime
> norm `p > 2`, `N(1−π)` is even when the residue field at 2 in `O_D` is `F₂`; so for **odd `N > 5`**
> one can *only* use `D ≡ 5 (mod 8)`.

Our (D1) was written in **existence** form ("prime-order CM curves exist exactly for `D ≡ 5 mod 8`"),
which survives — but the "exactly" bundles a cited half with an uncited half.

> **Regrade (D1):** **"Odd (hence prime, `N>5`) order ⇒ `D ≡ 5 (mod 8)`, i.e. 2 must be inert in the
> ORDER `O_D`" `[CITED — Bröker–Stevenhagen §2]`.** The converse — that such curves **exist** for
> *every* `D ≡ 5 mod 8` — is **empirical here** (`0` exceptions in `67,477` twists), **not cited**.
> **Delete the parenthetical "2 ∣ #E unless 2 is inert in the CM field."**

## 3. CONTRADICTED — a claim I made in conversation (not in any file)

I stated that "3 is a cubic residue mod `p` ⟺ `p = a² + 243b²`". **That is wrong: it is `4p`.**
Verified: `p`-form gives **2001 mismatches / 8988** (first failures `61, 67, 73, 103, 151, 193`);
**`4p`-form: 8988/8988, zero mismatches.** The trap is that the *2*-criterion legitimately uses `p`
(`p = a²+27b²`) while the *3*-criterion does not.

**Not present in any project file** (verified: no `243` anywhere in `btc_puzzle_investigation/*.md`), so
nothing needs editing — but it is exactly the failure mode
`feedback_verify_root_system_against_defining_polynomial_2026_07_20` names: a half-remembered classical
formula repeated on trust. Recorded so it is not repeated.

## 4. SUPPORTS (no action)

- **Eisenstein cubic reciprocity** — textbook form carries `N(π₁) ≠ N(π₂)` (Bröker/Shurman/DiVA Thm
  4.36); **our use satisfies it** (`N(ν)=n ≠ p=N(π̄)`). The norm-equal case is covered by Eisenstein's
  general law (DiVA Thm 4.48; Sun (1.3)). Coprimality/distinctness are not extra hypotheses.
- **Gauss's `2` criterion** `2` cubic residue mod `q` ⟺ `q = a²+27b²` — correct as used; attribution
  sharpened to **Euler conjectured, Gauss proved** (posth., Werke VIII).
- **Six orders by sextic class** — correct. Better citations than "Rajwade": **IR Ch. 18 §3 Thm 4**
  (trace via residue symbols), **arXiv:1212.1983 Thm 2.4** (the six explicit values),
  **Silverman–Stange Remark 25** (six ↔ `F*_q/(F*_q)⁶`).

## 5. PRIOR ART — this is the finding that most changes our grades

**Claim 7 (the bridge itself): NOT FOUND** in the sources reached — *reported as not-found, never as
novel*. But the search located a body of work far closer than §5 of the bridge document implied:

**J. Silverman & K. Stange, *Amicable pairs and aliquot cycles for elliptic curves* (arXiv:0912.1831).**
For `E: y²=x³+k` with CM by `ℤ[ω]` and `#Ẽ_p(F_p) = q`:
- **Theorem 19(a):** `ψ_E(p)(1 − ψ_E(p)) ≡ 1 (mod 3O_K)` — **this is essentially our (B3)**, the
  paired-unit fact that `ν` and `π̄` take the *same* primarizing unit.
- **Prop 23(b):** `(2/p)₆(2/q)₆ = (2/p)_Q(2/q)_Q` — **a two-sided `p↔q` sextic-symbol identity of
  exactly the shape of (B1)**, and its proof uses **our exact manoeuvre** ("there is a unique `ζ ∈ μ₆`
  such that `ζψ_E(p)` is primary … hence cubic reciprocity yields …").
- **Thm 7.1(d):** prime order `q` mod `p` ⇒ order `p` mod `q` iff `(4k/p)₆(4k/q)₆ = 1`.

**Babinkostova et al., *Elliptic Reciprocity* (arXiv:1212.1983), Thm 2.7:** "If `(p,q)_d` is an
elliptic pair, so too is `(q,p)_d`" — an established **Law of Elliptic Reciprocity**.

> **Consequences for our grades:**
> 1. **(B3) is PRIOR ART**, not ours — it is Silverman–Stange Thm 19(a) in different notation.
>    Regrade to `[CITED — Silverman–Stange arXiv:0912.1831 Thm 19(a)]`.
> 2. **(B1) sits inside an existing `p↔q` sextic-reciprocity literature.** The published identities are
>    at base `2` and base `4k`; the **base-`p`/base-`n`** instance was not found. That is a *much*
>    narrower gap than "not found in the literature" suggested, and the honest statement is:
>    **our bridge is an instance of a known family, at a base not located in the sources reached.**
> 3. **Outstanding and not done:** citation-graph sweep of the ~40 papers citing Silverman–Stange;
>    Lemmermeyer *Reciprocity Laws* Ch. 7; Cox *Primes of the Form x²+ny²* §4; MathSciNet/zbMATH.
>    **Until those are done, no novelty claim of any kind is supportable.**

## 6. Incidental finding — a record framing that should be deflated

`KNOWN_FACTS_*` describes secp's `b=7` class as **the** prime-order sextic class. For secp's own `p`
that is a checkable fact and is not disputed here. But **"exactly one of the six classes is
prime-order" is not a general law**: over primes `p ≡ 1 mod 6`, `p < 600`, the count of prime-order
classes is `{0: 6, 1: 31, 2: 12, 3: 1}`. **secp's "exactly one" is the typical case (~62%), not a
distinctive one** — it should not be carried as though it singled secp out.

## 7. Files needing edits from this audit

| file | edit |
|---|---|
| `RESULT_cubic_sextic_bridge_v1.md` | (B2) citation + upgrade to `[PROVED]`; (B3) → `[CITED — Silverman–Stange]`; §5 prior-art para replaced by §5 above |
| `RESULT_bridge_dichotomy_v1.md` | (D1) split into cited half + empirical half; delete "2 inert in the CM **field**" |
| `KNOWN_FACTS_*` (latest) | scope the "exactly one prime-order class" framing per §6 |

Per CLAUDE.md §1 the `v1` files are **not overwritten**; this audit is the correction of record and the
compendium carries the corrected grades.
