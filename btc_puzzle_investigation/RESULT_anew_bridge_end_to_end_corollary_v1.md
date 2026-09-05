# RESULT — the `A_new` bridge end-to-end: it can match MOV, never beat it (any curve)

*2026-08-06. Increment to `ANALYSIS_anew_bridge_n_visibility_v2.md` (canonical); nothing there is
revised. Answers a scoping question that v2 left implicit: v2 bounds the **first hop** (`j`), and
reports the secp branch as "factor 1 gain". This file composes the **second hop** and finds the
conclusion is not secp-specific. Exact integers; verification inline below. No leakage or ECDLP claim.*

---

## §1 The composition

The bridge is a two-hop route, and v2 only bounded hop 1:

- **hop 1** — get `d` into `A_new(F_{p^j})`. v2's theorem: needs `ord_n(p) | k·j`, `k ≤ 6`.
- **hop 2** — solve the `n`-DLP there by pairing, landing in `F_{(p^j)^{k_n}}` where `k_n` is the
  embedding degree **for `n`** over `F_{p^j}`, i.e. `k_n = ord_n(p^j)`.

The `k` of v2 is `A_new`'s embedding degree for **its own** order `ℓ | #A_new`. It is *not* the
embedding degree for `n`. Composing the two hops is what settles the question.

> **Corollary C.** `ord_n(p^j) = ord_n(p)/gcd(ord_n(p), j)`, so the end-to-end field degree over `F_p` is
> `j · ord_n(p^j) = lcm(j, ord_n(p))`.
>
> Since `ord_n(p) | lcm(j, ord_n(p))` for every `j`, **the bridge's final field always contains MOV's
> final field `F_{p^{ord_n(p)}}`.** Equality holds exactly when `j | ord_n(p)`.

**The bridge can match MOV; it can never beat it.** Not at secp, not at any `p`, not for any cover,
any `j`, any branch `m`. The first hop's `k ≤ 6` looked like a factor-6 saving in the exponent; hop 2
gives it back exactly, because attacking from an extension field raises the base of the exponent by the
same factor it lowers the degree.

**Note what Corollary C does *not* use:** supersingularity, `b₁=0`, the value of `m`, or anything about
`A_new`. It is the general fact that transferring into `F_{p^j}` first cannot undercut `ord_n(p)`.
v2's theorem does the different job of forbidding *small* `j`; Corollary C removes the remaining hope
that a small `j` would have helped if one had existed.

**Verification.** The identity `ord_N(p^j) = ord_N(p)/gcd(ord_N(p), j)` and its consequence
`j·ord_N(p^j) = lcm(j, ord_N(p))`: **354/354 cells**, `N ∈ {101, 257, 1009, 65537, 1000003, 15485863}`
× `j = 1..59`, exact integer orders, zero mismatches. At secp (`ord_n(p) = (n−1)/6`, 254 bits), the
end-to-end degree is 254 bits at `j ∈ {1,2,4}` and *larger* at `j ∈ {3,6,12,64}` — the bridge is
never below MOV and is often strictly worse.

---

## §2 So where does this shape of attack actually work?

Stated positively — the cover-transfer idea is sound; these are the conditions it needs.

1. **Through an ORDINARY factor, not a supersingular one.** GHS/Weil descent works because a factor of
   `Jac(C)` **shares Frobenius eigenvalues with `E`** — `Hom ≠ 0` — so the transfer is a genuine
   homomorphism and no embedding-degree gate applies. **Supersingularity, which is what made `A_new`
   look like the weakness, is precisely what makes it useless as a target:** supersingular ⇒ eigenvalues
   `√p·ζ` ⇒ the factor's order divides `p^k−1` for `k ≤ 6` ⇒ `n` cannot live there unless `ord_n(p)`
   is already tiny, in which case MOV on `E` already works. The two properties are the same property.
2. **Over a field with a proper subfield.** GHS needs `F_{q^n}`. secp is a **prime** field — already on
   the record (placement map field 1: Weil descent inapplicable, no proper subfield). This is the
   binding obstruction for the *working* version of the attack, and it is not the one the `A_new`
   proposal was trying to route around.
3. **Where the cover's own genus stays low.** Route 3/N4 (`Õ(p^{4/3})` for one cover, not a family
   bound) is the live version of this on our object, and Corollary C does not touch it — index calculus
   on `Jac(C)` needs no `n`-visibility in `A_new`. `[OPEN]`.

**Constructive rather than cryptanalytic.** Small embedding degree is the property one *builds* pairings
from; supersingular abelian surfaces are pairing **sources** in the literature, not attack targets. So
`A_new` is a pairing-friendly abelian surface canonically attached to secp256k1's curve equation. Its
group order is `p²+p+1` (at `m=1`), coprime to `n` in the relevant sense — so it yields **no** pairing on
secp's own group, and no protocol use for secp follows from it either. Recorded so the object is not
re-proposed in the constructive direction on the assumption that it was left unexamined.

---

## §3 The gate as a reusable instrument

The screening test costs one line and settles the whole proposal class before any map is constructed:

> Given a curve `E/F_p` of prime order `n` and a claimed easy factor `A` of a cover's Jacobian: read `k`
> off `A`'s characteristic polynomial, and compare with `ord_n(p)`. If `ord_n(p) ∤ k·j` for every usable
> `j`, no transfer of the affine-log class exists — **no map need be built, and none can be.**

This applies to any "an easy factor lives in the cover" proposal, on any curve, and it is decidable from
two integers.

---

## §4 Scope — what Corollary C closes and what it leaves

| | |
|---|---|
| **OBJECT** | The two-hop route: `⟨G⟩ → A_new(F_{p^j}) →` pairing `→ F_{p^{jk_n}}`. |
| **CLASS closed** | Transfers of v2 §5's class **whose second hop is a pairing**. Power 1 — deterministic. |
| **SCOPE** | Any `p`, any `j`, any branch. Not secp-specific. |
| **UNTOUCHED** | Everything v2 §6 lists, unchanged, and Corollary C adds no reach over any of it: (1) set-injective encodings not factoring through `ℤ/n` — **power 0**, they never reach hop 2; (2) CRT recovery of `d mod M`, `gcd(M,n)=1` — **power 0**, same reason; (3) **D2**, the Lang-torsor twist bridge — a statement about values of `V(a)`, no hop 2 at all; (4) **Route 3/N4** index calculus — needs no `n`-visibility. A non-pairing weakness in supersingular surfaces would also fall outside this, and would be a different proposal from the one analysed. |

---

*Gates: this file adds a proof plus a 354-cell identity check, promotes nothing, and consolidates
nothing — `compile-diff` not applicable. No citation is load-bearing (GHS/Weil-descent placement is
quoted from our own placement map, itself `[CITED — verified]`).*
