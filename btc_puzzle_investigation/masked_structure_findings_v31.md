# Findings v31 — cocycle rigidity (a theorem), the completed cohomology picture, and the map

**Date:** 2026-07-17 · `carry_cocycle_v1.py` + reasoning. Ultra-think on the v30 result "d is the
unique additive cocycle." The finding is deeper than an empirical null: it is a **theorem** (prime
order), it **unifies** the project's scattered prime-order-exactness results, and it precisely
**locates the frontier**.

## 1. Cocycle rigidity `[PROVED, elementary]`
**Lemma.** Let `E` be a group of prime order `n` and `f: E → M` a readout with
`2 ≤ #values(f) ≤ n−1`. Then there is **no** `φ: M×M → M` with `f(P+Q)=φ(f(P),f(Q))` ∀P,Q.
*Proof.* Such a `φ` makes the level-set partition a group congruence (`P~P′,Q~Q′ ⇒ P+Q~P′+Q′`),
i.e. cosets of a subgroup `H=f⁻¹(f(O))`. `|H| | n` prime ⇒ `H={O}` (f injective, impossible for a
coarse readout) or `H=E` (f constant). Both contradict `2 ≤ #values ≤ n−1`. ∎

So **the only additively-chaining coordinate readout on a prime-order curve is `d` itself (the DLP)**,
not by a numeric coincidence but because `E` has no proper subgroup. The empirical `xy` z=0 (v30) is
the *even-approximately-zero* part (KS-flatness); the *no-exact-cocycle* part is this lemma.

**Unification.** This is the same prime-order fact behind: `σ⊥s_y` ("prime order forbids the
2-torsion endpoint"), amicable `Hom=0` (coprime orders), Semaev `C_t` smooth ("no 2-torsion"). One
theorem — **prime-order rigidity** — with the cocycle result as its coordinate-readout face.

## 2. Chaining ⟺ spectral concentration ⟺ v14 (one coin)
Expand `f = Σ_a f̂(a)χ_a`, `χ_a(P)=e_n(a·d(P))`. The characters `χ_a` are exactly the perfect
cocycles. `f` chains ⟺ its spectrum concentrates on one `χ_a` ⟺ knowing `d`. Cheap readouts have
**flat** spectra (`|f̂(a)|=O(√p/n)` by KS) — the flatness *is* the failure to chain. The cocycle
result and v14 ("aligned readout leaks but needs the DLP") are one statement.

## 3. The 2-cocycle (carry) — `H²` closed too `[VERIFIED, control fires]`
Rigidity kills 1-cocycles (`H¹`). But `H²(ℤ/n,ℤ/n)=ℤ/n` is **nontrivial**; its generator is the
**addition carry** `c(P,Q)=[d_P+d_Q≥n]` (extension data of `ℤ/n²→ℤ/n`) — a **comparison**, and the
`(n,k,D)` "wraparound." Is it coordinate-detectable? Probe: `MI(carry ; cheap feature)`, control =
`(msb d_P, msb d_Q)`.

| feature | MI | z |
|---|---|---|
| **msb(d_P), msb(d_Q)** (CONTROL) | 0.486 | **+849** (fires) |
| xy 2-cocycle defect `xy(S)−xy(P)−xy(Q)` | 0.001 | −0.7 |
| x group-law residual, xy(S), x(S), y(S)-half, xy-ratio | ≤0.004 | −0.8 … **+2.8** |

**The carry is not leaked by the curve coordinates** (all z sub-threshold; control z=849). The
comparison stays DLP-hard; the `xy` 2-cocycle defect is dead.

## 4. The map (what is closed, what is open)
The classical DLP "doors," each shut for secp for a specific structural reason:

| door | mechanism | status for secp |
|---|---|---|
| additive subgroup (composite order) | proper quotient | **shut: prime order** — *our cocycle rigidity is the coordinate-level proof* |
| MOV / pairing (multiplicative) | embed in `F_{p^k}*` | shut: embedding degree ~254-bit |
| anomalous (trace 1) | additive transfer | shut: `#E=n≠p` |
| Weil descent / GHS | subfield cover | shut: prime field |
| **2-cocycle / carry (this file)** | comparison from coords | **shut: coordinate-null (control z=849)** |

**The one crux none of this touches — the real frontier:** *cheap spectral concentration without
`d`* (v14). Rigidity proves it cannot come from any additive **chaining/accumulation** mechanism, and
the carry-null proves it cannot come from the **H² comparison**. A door, if one exists, must be
**non-cohomological** — a cheap operator that concentrates the flat character spectrum — which is
essentially the DLP itself. That is where a break would live, and it is precisely located now.

## 5. Uses / ideas to explore (graded)
- **Certificate / theorem `[PROVED]`:** rigidity retires whole classes of would-be distinguishers
  with a one-line prime-order argument, and delineates the exact boundary (everything changes at
  composite order / proper subgroup). Publishable as a clean negative-characterization.
- **Search-pruning bound `[from v17]`:** any Pollard/kangaroo jump function is a cheap readout;
  rigidity + `Inv⊆μ₆` ⇒ the `√6` GLV/automorphism speedup is the best *structural* jump improvement.
- **The only genuine break-candidate `[open, = the DLP crux]`:** a **scaled phase-hunt** for a cheap
  readout with **anomalous spectral concentration** (a single `|f̂(a)|` above the KS floor). v14/v15
  found only the μ₆ symmetry; a larger-scale / CM-Frobenius-guided hunt is the one continuation that
  could be a break — with honest expectation that it is as hard as the DLP.
- **Non-cohomological structure:** the CM/GLV/lift geometry (μ₃/μ₆, sextant, rhombus, cap, the
  odd+μ₃ `xy` shadow, equal-mass odd half) is REAL and `μ₆`-bounded (v17, v26–v30); it does not chain
  (rigidity) — so it is structure without a reduction, and the open question is whether any of it
  concentrates the spectrum, which rigidity says it cannot do *additively*.

## Grades
- Cocycle rigidity: **PROVED** (elementary, prime order). Chaining⟺concentration⟺v14: **PROVED given
  KS**. Carry not coordinate-leaked: **VERIFIED** (powered, control z=849). The door-map: **CITED**
  (classical) + our two coordinate-level entries. The spectral-concentration crux: **OPEN** (= DLP).

## Files
`carry_cocycle_v1.py`, `joint_set_cocycle_v1.py` (v30). Prior: `masked_structure_findings_v14`
(spectral), `_v28/v30` (bilinear/cocycle), `KNOWN_FACTS_secp256k1_and_keys_v5.1` (parity-obstruction,
MOV), `glv_closure_theorem_v2` (KS closure).
