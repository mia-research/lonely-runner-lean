> # ⚠ PARTIALLY SUPERSEDED 2026-09-04 — the corrections stand; the framing does not.
> An earlier blanket "withdrawn" header I added today was too coarse and is removed.
>
> **STANDS** (and is the reason to keep this note): §4's correction of M38 — the pointwise form's
> extra Fourier coefficient is **vacuous**, and the composite-`n` primes are still cyclic, hence still
> one branch. Also §5: secp is cyclic ⇒ `m=+1` is **forced**, not observed.
>
> **DOES NOT STAND:** §6's claim that N8 is "correctly scoped for the first time". The even-`n`
> failure was already a **firing control** in `NOTE_n8_pencil_reduction_v1.md` (2026-09-01, 21:57),
> which reports `n` EVEN failing at *every* `R` on 3 curves — and states the hypothesis in the more
> general form **`n` odd ⟺ `x³+Ax+B` irreducible**, valid for any `(A,B)`, not just `B=7`. My
> `m = −2 ⟺ 7 a cubic residue` link is a `j=0`-specific corollary of theirs, not a new scoping.

# NOTE — N8 / M21 is a statement about ONE branch: `m = −2` forces `E(F_p)` non-cyclic, so the whole corpus has only ever tested `m = +1` — and the identity is FALSE on the other branch

*2026-09-02. Corrects `NOTE_n8_pointwise_convolution_v1.md` (yesterday, mine) and scopes **M21** /
**N8**. Script `n8_branch_confinement_v1.py`. Exact integer throughout. **No leakage / ECDLP /
keyspace claim.***

---

## 1. The structural fact `[PROVED — elementary]`

For `p ≡ 7 mod 12` (so `p ≡ 1 mod 3`), `E : y² = x³ + 7`:

> `7` is a cubic residue mod `p`  ⟹  `−7` is a cubic residue (`−1 = (−1)³` is always a cube)
> ⟹  `x³ + 7 = 0` has **three** roots in `F_p`  ⟹  `E[2] ⊆ E(F_p)`  ⟹  **`E(F_p) ⊇ (Z/2)²`, non-cyclic.**

By the m-law (`RESULT_mlaw_theorem_secp_class_v1.md`), `7` a cubic residue is exactly `m = −2`. So:

> ### **`m = −2` ⟹ `E(F_p)` is non-cyclic.  Equivalently: `E(F_p)` cyclic ⟹ `m = +1`.**

**Verified, `p ≡ 7 mod 12`, `p < 700`: zero exceptions** on the forward chain (every `7`-cubic-residue
prime has `x³+7` splitting, full rational 2-torsion, and a non-cyclic group).
**The converse is FALSE** and is not claimed: `p = 199, 271, 379` are non-cyclic via *odd* torsion
(`#E = 189, 243, 343`) while having `m = +1`.

## 2. Why this scopes the entire N8 / M21 corpus

`h₁` and `h₂` are indexed by the **discrete logarithm** — `h₁[d] = χ₂(y_{[d]G})` — which presupposes
a **cyclic** `E(F_p)`. By §1, cyclic ⟹ `m = +1`. Therefore:

> ### The `h₁/h₂` framework **cannot see `m = −2` at all.** M21's 1171 μ₆-orbit cells across 11 primes
> ### `43 ≤ p ≤ 1303`, and my own 11 primes yesterday, are **all in the single branch `m = +1`.**

This is a scope fact the corpus does not record anywhere.

## 3. The other branch, tested for the first time — and the identity FAILS there

Convolution needs only a finite **abelian group**, not a cyclic one. Re-indexing `h₁, h₂` by the group
element itself makes `m = −2` testable:

| p | `#E` | m | `f[P] , P ≠ O` | `f[O]` | `−2·leg·p` | |
|---:|---:|---:|---|---:|---:|---|
| 43 | 31 | +1 | `{0}` | 86 | 86 | EXACT |
| 67 | 79 | +1 | `{0}` | 134 | 134 | EXACT |
| **19** | 12 | **−2** | `{−24,−20,0}` | 32 | 38 | **FAILS** |
| **223** | 252 | **−2** | 21 distinct values, `−88 … +80` | 440 | 446 | **FAILS** |
| **331** | 364 | **−2** | 28 distinct values, `−128 … +144` | 656 | 662 | **FAILS** |
| **367** | 372 | **−2** | 29 distinct values, `−168 … +152` | 728 | 734 | **FAILS** |

It does not fail by a constant offset — `f` acquires a **wide spread** off the identity. So

> ### **M21 / N8 is a property of the `m = +1` branch, not a general identity.**

## 4. The `a = 0` coefficient is VACUOUS — a correction to my own note

At `p ≡ 3 mod 4` the points `(x, ±y)` pair up and `χ₂(−1) = −1`, so `Σ_P h₁[P] = V₁(0) = 0`
(measured: every prime). And by the same quartic-character computation that drives the m-law,

> `V₂(0) = Σ_{Q ∈ E(F_{p²})} χ₂^{(2)}(y_Q) = 2·Re(S) = 2·m·p`  *(measured: `43,67,79,19,223,331` — exact)*

so `f̂(0) = V₂(0) − V₁(0)² = 2mp`, while the identity claims `−2·leg·p = +2p`. **These agree iff
`m = 1`** — which §1 says is *forced* on every prime the framework can index.

> **Correction to `NOTE_n8_pointwise_convolution_v1.md` §2 ("far more is true").** Wrong, twice.
> (a) The pointwise form is Fourier-at-`a≠0` **plus exactly one coefficient**, not "far more".
> (b) That one coefficient is **vacuous on the testable domain**: it restates `m = 1`, which cyclicity
> forces. It is not independent evidence for anything.
>
> **Correction to v1 §3 ("scope gain … not a cell artefact").** Weaker than stated. `p = 103, 139,
> 151, 193` have composite `n` (111, 147, 133, 219) but are still **cyclic**, hence still `m = +1`.
> They do broaden the test beyond μ₆-**orbit cells** — that part stands — but **not beyond the
> branch**, which is the scope limit that actually matters.

## 5. secp

`#E(F_{p_secp})` is prime (cofactor 1) ⟹ **cyclic** ⟹ by §1, `m = +1`, and directly:
`7^{(p−1)/3} ≢ 1`, `7` a cubic non-residue. So the corpus's **measured** `m = 1` at secp is now
**forced** — a consequence of the group being cyclic, not an observation. secp sits in the branch
where M21/N8 holds.

## 6. What this does to N8 as a target

> ## ⚠ SELF-CORRECTION, same session — §6's hypothesis was WRONG. The condition is `n` ODD.
>
> §6 below says *"any proof must invoke `E[2] ⊄ E(F_p)`"*. **That is not the right condition.**
> Discriminating test (`n8_hypothesis_discriminator_v1.py`, group-indexed, exact):
>
> | family | `#E(F_p)` | rational 2-torsion | identity |
> |---|---|---|---|
> | `p≡7 mod12`, `7` non-residue (`m=+1`): `31,43,67,79,103` | **odd** | **none** (`x³+7` irreducible) | **EXACT** |
> | `p≡1 mod12`: `61, 97` | **odd** | none | **EXACT** |
> | `p≡11 mod12`: `11,23,47,59,71,83,107` | even | **exactly one** (`x³` is a bijection ⇒ 1 root) | **FAILS** (5–19 distinct values off `O`) |
> | `p≡7 mod12`, `7` residue (`m=−2`): `19, 223` | even | **full `E[2]`** | **FAILS** |
>
> The `p ≡ 11 mod 12` rows satisfy `E[2] ⊄ E(F_p)` and **fail anyway**. So:
>
> ### The hypothesis is **`E(F_p)[2] = {O}`, i.e. `#E(F_p)` ODD** — equivalently `x³+7` irreducible
> ### mod `p`. Not "not-full-2-torsion". A *single* rational 2-torsion point already breaks it.
>
> **This also widens the identity's home:** it is **not** confined to `p ≡ 7 mod 12` — `p = 61, 97`
> (`≡1 mod 12`, `n` odd) satisfy it. And it **excludes the whole `p ≡ 11 mod 12` arm**, where `n` is
> always even (`x³` bijective on `F_p` when `p≡2 mod3` ⇒ `x³+7` has exactly one root ⇒ one rational
> 2-torsion point). §1–§5 above are unaffected: `m=−2 ⇒ non-cyclic` still holds, and the corpus is
> still confined — the confinement is just *tighter and differently described* than §6 said.
>
> **Candidate mechanism, now visible.** `ψ(P) := χ₂(y_P)` vanishes exactly at `O` **and at every
> rational 2-torsion point** (`y = 0`). With `n` odd, `ψ` is nonvanishing on all of `E(F_p)∖{O}` and
> takes values in `{±1}`; each rational 2-torsion point punches an **extra zero** into `ψ`, and the
> convolution `ψ⋆ψ` loses exactly those terms. That — not the group structure per se — is the likely
> reason the identity breaks. Also with `n` odd, multiplication by 2 is a **bijection** on `E(F_p)`,
> so `φ(Q) = R−Q` has exactly **one** rational fixed point for every `R`, which is what makes the
> `Fix(Frob)` / `Fix(φ∘Frob)` orbit bookkeeping of §6 come out even.
>
> **Superseded text follows, kept for the trail.**

N8 (prove the identity) is **not** dead — it is **correctly scoped for the first time**, and the
scoping is a constraint a prover can use:

> Any proof of N8 **must invoke the branch hypothesis** (`E[2] ⊄ E(F_p)`, equivalently `x³+7`
> irreducible-or-not-split, equivalently `m = +1`). A proof that does not use it **is wrong**, because
> §3 exhibits counterexamples. This tells the prover *where the hypothesis has to enter* — which the
> twist-comparison framing of `NOTE_..._pointwise_convolution_v1.md` §4 did not know.

The §4 reformulation there (both sides sum `w(Q) = χ₂(y_Q·y_{R−Q})`, one over `Fix(Frob)`, the other
over `Fix(φ∘Frob)`, `φ(Q) = R−Q`) is **unaffected and still correct** — it is an identity of summands,
not of sums. The full 2-torsion is exactly what changes the fixed-point structure of `φ`, since
`φ`'s fixed points are the solutions of `2A = R`. That is the likely mechanism, and it is where to look.

## 7. Grades

| item | grade |
|---|---|
| `m = −2 ⟹ E(F_p)` non-cyclic (§1) | **`[PROVED — elementary]`**, 0 exceptions `p<700` |
| the converse | **FALSE** — `199, 271, 379` |
| M21/N8 corpus confined to `m = +1` (§2) | **`[PROVED]`** — a corollary of §1 and the dlog indexing |
| identity FAILS at `m = −2` (§3) | **`[VERIFIED — exact, 4 primes, group-indexed]`** |
| `V₂(0) = 2mp`, hence `a=0` vacuous (§4) | **`[PROVED — elementary]`**, measured exact |
| secp forced into the `m=+1` branch (§5) | **`[PROVED]`** |

**Owed:** `compile-diff` if folded into a master. N8 itself remains open, now with its hypothesis named.
