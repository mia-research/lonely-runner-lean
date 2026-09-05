# Literature sweep — the ★ overdue item, partially discharged

**Date:** 2026-07-25 · `citation-verifier`, scoped to 5 priority targets (a prior attempt died on a
session limit). **Items 1, 2, 5 completed; items 3, 4 NOT REACHED.** Sources actually opened are listed
per item; where the primary text was not obtained, that is stated and **no grade moves**.

---

## 1. `p ↔ #E(F_p)` reciprocity for `y²=x³+k` — **PUBLISHED** (and the record already knew part of this)

**Silverman & Stange, *Amicable pairs and aliquot cycles for elliptic curves*, arXiv:0912.1831v1
(Exp. Math. 20(3), 2011), Theorem 19(a)–(d) p.16, Remark 20, Proposition 23 p.19** — read verbatim.
For `E: y²=x³+k` with CM by `O_K` and primes `p,q≥5` of good reduction with `#Ẽ_p(F_p)=q`:

> (a) `p` splits, `ψ_E(p)(1−ψ_E(p)) ≡ 1 (mod 3O_K)`; (b) `q=(1−ψ_E(p))O_K` splits;
> (c) `1 − ψ_E(p) = (4k/p)₆ (4k/q)₆ ψ_E(q)`; (d) `a_q(E) = ε(q+1−p) ⟺ (4k/p)₆(4k/q)₆ = ε`.

Prop. 23's proof contains the record's own manoeuvre verbatim (multiply `ψ_E(p)` by the unique `ζ∈μ₆`
making it primary, then apply cubic reciprocity). **This is a two-sided sextic-symbol reciprocity
between `p` and the curve's order — the object the record calls the "bridge".**

⇒ **The right citation for (B1) is Silverman–Stange Thm 19 / Prop. 23**, at bases `4k, k, 2`. The
record's (B1) is at bases `p` and `n`; that difference is the only gap. The record's
`[VERIFIED — classical]` grade and its **"no originality claimed"** stance both stand unchanged; only
the pointer improves. (Thm 19(a) is the record's (B3) verbatim — already correctly regraded in
`AUDIT_citation_verification_v1.md §5`.)

### ⚠ DO NOT cite "Lemmermeyer Thm 7.10 = sextic reciprocity in ℚ(ω)" — the number is DISPUTED

Two independent secondary sources assign **different statements** to that number, and **the primary book
was not obtained** (archive.org, Heidelberg, Bilkent, Springer all failed):

- **Silverman–Stange** (proof of Lemma 32): *"the sextic reciprocity law for Q(ω) as stated in
  [Lemmermeyer, **Theorem 7.10**]"* — the **main law** for E-primary `α,β`.
- **Gao–Zhao**, arXiv:2201.01885v2 §2.1: cites **Lemma 7.9** for the main law and
  **"[24, Theorem 7.10]"** for the **supplementary laws** (`(−ω/n)₆`, `(2/n)₂`).

Both agree the material is **Lemmermeyer Ch. 7 §7.3, "E-primary"**. Acceptable form:
*"Lemmermeyer, Ch. 7 §7.3, sextic reciprocity in ℚ(ω) for E-primary elements, as quoted by
Silverman–Stange [0912.1831, proof of Lemma 32]"* — **attributed, not verified.**

**Also: the E-primary normalization is NOT the record's.** Lemmermeyer/SS use *E-primary*
(`≡ ±1 mod 3` **and** a mod-4 condition on `α³`); the record's `c₃ = s·(e(π̄′)−e(ν′))` comes from
**primary** (`≡ 2 mod 3`) only. The correction terms are structurally different objects, so the
published law does **not** hand over `c₃` directly.

## 2. Cap Law — the automorph half is **CLASSICAL**; the flap identity was not located

**ETH Zürich 401-4110-19L, *Binary Quadratic Forms and the Class Number Formula*, Theorem 1.12, p.6**
(read; underlying result is Gauss): automorphisms of a binary quadratic form correspond to Pell
solutions `t²−du²=4`, and **for `d=−3` there are exactly six** — hence an order-3 automorph with
`tr=−1`, `det=1`, given by a fixed integer matrix independent of `p`.

⇒ **`cap_law_proofs_v1.md` Theorem A steps 1+3 should be regraded
`[PROVED — classical input: the automorph group of a disc-−3 form has order 6]`.** The record's
`M=[[0,−1],[1,−1]]` is one presentation of that classical object.

⚠ **NOT located: Lemma C**, the flap identity `P ∖ (P∩ωP∩ω²P) = {|u−v|>½}` for the **half-open
parallelogram** `P`. The Eisenstein-lattice literature the record points at concerns the **Voronoi
hexagon**, a *different* fundamental domain. **Lemma C keeps its current standing.**

## 3–4. `|FLD|=6h(−p)` / the two general character-sawtooth laws, and `H1` — **NOT REACHED**

**No primary text was opened for either.** Candidates located but not read: Berndt & Evans, *Dedekind
sums and class numbers*, Monatsh. Math. **84** (1977) 265–273; Berndt, *Character analogues of the
Poisson and Euler–Maclaurin summation formulas*, J. Number Theory **7** (1975) 413–445; Goldstein–Razar,
Nagoya Math. J. **63** (1976) 93–121. PDF fetches for item 4 timed out.

⇒ **NO GRADE MOVES IN EITHER DIRECTION on items 3 and 4, and the ledger's ★ item stays OPEN for them.**
Note also: the record's `[CITED — classical]` on the anchor `h = −(1/p)Σχ₂(a)a` is **unverified by this
sweep**. "Not reached" ≠ "no prior art".

## 5. secp as an amicable pair — no prior art for secp, **but the framing must narrow**

- **Not located:** any publication stating that `(p,n)` is an amicable pair for secp256k1's `y²=x³+7`.
  Bounded search (3 query families + 2 targeted fetches) ⇒ **`NO PRIOR ART FOUND`, which is weak
  evidence, not an absence.** May simply be uncomputed folklore.
- **★ DOES exist and matters:** the **Pallas/Vesta ("Pasta") curves** (`github.com/zcash/pasta`, README
  read verbatim) are *"the **amicable pair** of prime-order curves … `Ep: y²=x³+5` over `GF(p)` of order
  `q` (Pallas) … `Eq: y²=x³+5` over `GF(q)` of order `p` (Vesta)"* — a **deliberately constructed,
  widely deployed, 254-bit `j=0` amicable pair**, found by a public `amicable.sage` search script.

⇒ **Any phrasing implying that a named/standardized cryptographic curve being an amicable pair is
unremarked is WRONG.** The defensible residue is only: *"secp256k1's own instance is not located in the
sources reached."* And `RESULT_secp_amicable_pair_v1.md §2`'s sextic-twist-selection observation should
note that **Pasta demonstrates such twist selection can be, and has been, done by construction.**

- **Independent re-verification of the underlying fact** (agent's `amic2.py`, exact integers,
  Tonelli–Shanks): over `F_n`, `p·P = O` for 3 random points on `y²=x³+7`, control `(p+2)·P ≠ O` for all
  three; `p` prime ⇒ `#E(F_n)=p`. **The record's fact is correct.**

## Net effect

| item | grade movement |
|---|---|
| (B1) cubic bridge | none — already `[VERIFIED — classical]`, no originality claimed. **Citation improved** to Silverman–Stange Thm 19 / Prop. 23. |
| Cap Law Thm A steps 1+3 | **gains a classical-input citation** (disc-−3 automorph group order 6). Lemma C unchanged. |
| `|FLD|=6h`, `(†)`, general laws, `H1` | **none — NOT REACHED.** ★ item stays open. |
| secp amicable | fact re-verified; **framing narrowed** — Pasta is published prior art for the *concept applied to a named `j=0` curve*, though not for secp itself. |

**The ★ ledger item is PARTIALLY discharged (3 of 5 targets), not closed.**
