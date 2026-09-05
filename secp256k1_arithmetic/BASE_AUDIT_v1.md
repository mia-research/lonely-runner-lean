# Base-problems audit (2026-07-11)

Requested: "make sure we are not have base problems too." A foundation check of
everything the secp256k1 arithmetic study and its spectral extension rest on —
separating what is **solid** from what has a **known load-bearing gap**, so nothing
downstream is silently built on a broken step. Two ledgers, kept separate.

---

## Ledger A — the CM arithmetic study (SOLID, gap-free)

`secp256k1_arithmetic_v3.md` and its threads. Everything here is either classical
CM theory or an exact computation, and **none of it depends on the RH programme.**

| Result | Foundation | Base status |
|---|---|---|
| Formal group log `Σ 7^k C(3k,k)/(6k+1) T^{6k+1}` | exact power series from `w=z³+7w³` | **solid** — exact, `verify_v1.py` A1–A4 |
| Hecke character `χ = −(28/π)₆⁻¹` | Jacobi-sum Grössencharacter + sextic reciprocity | **solid** — *derived*, 1442/1442 (thread A) |
| Amicable closure `ρ_k = ½(1/3+R(k))` | Silverman–Stange Conj 40+27 | **solid** — exact-rational match, 12 classes |
| GLV = `(π_n)` | CM ideal / commuting Frobenius | **solid** — exact, `verify_v1.py` G |
| Three-term ASD, mod-ℓ³ locus `{a_ℓ=±1}` | Honda congruence | **solid** — 147/147 (thread C) |
| Zeros of `L(ψ,s)` | CM theta series → L-function | **solid** — LMFDB-matched (thread E) |
| BSD `L(1)=Ω, ∏c=Ш=1` | rank-0 CM BSD (theorem) | **solid** — `L(1)/Ω=1` (thread D) |

**Computational base re-verified** (`thread_spectral_v2.py`, B1–B3):
`a_n` matches LMFDB q-expansion `q+7q¹³+8q¹⁹−5q²⁵+…`; multiplicativity
`a_{mn}=a_m a_n`; functional equation `Λ(s)=WΛ(2−s)` to <1e-15. So the L-function
object the zeros come from is correct at the base.

**Conclusion A:** the study stands on classical theory + exact computation. No gap.

---

## Ledger B — the φ(n)-residue RH programme (TWO fatal gaps; does NOT prove RH)

Separate work (8 Zenodo records), bridged to the curve only via `L(ψ,s)`. Per its
own walked-back chronology (KNOWN_FACTS §12) and the analysis re-verified here:

1. **Forcing (Moment-Pumping) is broken** — the moment the argument needs to
   *grow* actually *decays*. This is fatal to the RH-proof claim. **The programme
   does not prove RH.**
2. **Operator foundation** — `Ĥ=πA²` on `[1,∞)` has deficiency indices **(1,1),
   not (0,0)**; `A` itself is **(1,0)** (no self-adjoint extension — Stone fails,
   the dilation is a semigroup). Independently re-verified this session
   (`radial_selfadjointness.md` check). The full-line fix restores
   self-adjointness but **empties `D_φ` to {0}** under the normalized multiplier —
   a normalization clash + the circle/line incompatibility.

**What in Ledger B is still solid** (checked): the coercivity constant
`1/12 = min 1/φ(q) = 1/φ(13)` (a theorem); the Eisenstein–Ramanujan **survival law**
(μ₆ = six units survive — verified `verify_v1.py` I); the norm-form identity
`Σ(r/6)N^{−s}=ζ_K(s)`; the function-field Hilbert–Pólya instance (Frobenius on the
Tate module, Weil pairing). These are genuine and independent of the two gaps.

**Retracted / corrected in Ledger B** (do not restate as results): "wall invariant
∝ degree" (→ tracks Selberg `n_L`); "n_t spectrally optimal" (loose frame,
`μ(n_t)=0` liability); ZFR rank-2 common mode (bug; real rank-1); "inverted sieve
computes Iwasawa μ" (speculation).

**Conclusion B:** the RH *proof* is not established — two load-bearing gaps. This
is already documented; the audit confirms it and confirms Ledger A does not touch
it.

---

## The interface — and a base error caught in MY OWN spectral write-up

The only place Ledger A meets Ledger B is the study's §6 (survival law) and the
spectral-realization map. **Base checks on that interface:**

1. **The study §6 does not rely on the broken forcing.** It is explicitly a
   *consistency/model* result ("not the zeros; positivity open"). It does **not**
   claim the wall forces RH. ✓ Correct scoping — no inheritance of gap 1.

2. **Corrected: the operator model's self-adjointness caveat is now stated.** The
   `Ĥ_CM = π(A_r²+A_θ²)` model has the **radial (1,1) defect** on `[1,∞)` (gap 2);
   only the compact angular `A_θ` is genuinely (0,0). `SPECTRAL_REALIZATION_v1.md`
   §2 now flags this explicitly rather than implying a clean e.s.a. operator.

3. **Caught this session — I had propagated the v1 conflation into my own doc.**
   My `SPECTRAL_REALIZATION_v1.md` §2 originally wrote "the six angular sectors are
   the six ray-class characters, and χ selects one." **That is the same
   archimedean-vs-finite μ₆ conflation I flagged in `adelic_recasting_v1.md`.**
   Fixed: the six `A_θ` sectors are **archimedean angular** modes (continuous
   S¹, ∞-type angle `θ_p=50.55°`); the finite χ is a **separate, discrete,
   finite-place** ray-class character. They are Pontryagin-dual, not equal. Both
   `SPECTRAL_REALIZATION_v1.md` and `adelic_recasting_v2.md` now state this
   correctly.

4. **The conductor is a finite-place object** (base of the density/`log N`), not
   in the archimedean `ℂ^*` — so the CM place does not make the finite places
   dispensable. Stated in v2.

---

## Net

- **Ledger A (the study): no base problems.** Classical CM theory + exact
  computation; the L-function base (a_n, Λ, functional equation) re-verified.
- **Ledger B (RH programme): two known fatal gaps** — does not prove RH; correctly
  kept separate; the study never leans on it.
- **Interface: two base errors fixed this session** — (i) my own archimedean-vs-
  finite μ₆ conflation, (ii) the un-flagged radial-(1,1) caveat in the operator
  model. Both now stated. The spectral map claims exactly what is proven (explicit
  formula, local HP, LMFDB-matched zeros) and no more.

The honest one-line: **the arithmetic is solid; the spectral realization is
correctly scoped as open; and the two places I could have inherited a base error
(the μ₆ conflation and the operator-self-adjointness caveat) are now corrected.**
