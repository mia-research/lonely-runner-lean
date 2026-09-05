# Masked-Structure — Findings v11: the three un-ruled-out lines, investigated

**Date:** 2026-07-16 · the three lines that neither the `|Aut|=6` ceiling nor the
`O(p^{-1/2})` equidistribution ceiling excludes. Mindset: unproven ⇒ investigate.
Scripts: `easy_target_predict_v1.py`, `amicable_transfer_v1.py`.

## Line 1 — easy-target predictability: no lever (and a trap caught)

v10 found the decomposition count over-dispersed (some targets decompose more ways). A
target-selection lever would need a **cheap readout of R** to predict high `c(R)`. Decisive
question (disjoint attribution): is easy-target-ness a property of **R** (intrinsic ⇒ lever)
or of the **(R,F) pairing** (F-specific ⇒ no lever)?

- **Test A (random F):** `Var_R(c̄)/sampling-noise = 1.1` — flat. Over random bases every
  target has the same expected `c` (matches translation-covariance: `F+Q` is an
  equidistributed base for every `Q`). Not intrinsic.
- **Test B (β-invariant F) looked positive:** `MI(c ; norm_R)=0.44 bits`, shuffle-null
  `p=0.005`. **Audited hard, and it failed:** (i) the random-F c̄ is provably flat yet still
  gives `MI=0.32` → MI~0.3–0.5 is the estimator's bias floor at M=150; (ii) decisive —
  per-base `Spearman(norm, c)` across 80 independent β-invariant bases has **mean ≈ 0**
  (−0.010 / +0.004), `frac>0 = 0.44–0.54` (coin flip). The correlation is **F-specific**
  (real for one base, random sign across bases), not R-intrinsic. `Var_R(c̄_β)/noise = 0.85`
  (flat) confirms it.

**Verdict:** no target-selection lever. Easy-target-ness is a pairing artifact, provably flat
over F, for random *and* β-invariant bases. **Trap caught:** the single-F shuffle-null fired
(p=0.005) but the cross-F sign test killed it — the residue-vs-component discipline exactly.
I nearly reported Test B as a lead.

## Line 2 — amicable algebraic transfer: a NARROW sub-case walled; the real question is a FENCE

**Correction (wall vs fence discipline):** an earlier draft said this "found the precise
wall." It did not. What is rigorously true is a *narrow* sub-case, and it is arguably not
even the relevant mechanism.

Real small amicable pairs for `y²=x³+7` exist and are structurally identical to secp:
**(67,79), (907,967), (1249,1303), (2089,2143)** (`#E(F_p)=n`, `#E(F_n)=p`).

**Rigorously proven (a real but narrow theorem):**
> `E(F_p) ≅ ℤ/nℤ`, `E(F_n) ≅ ℤ/pℤ`, `gcd(n,p)=1` ⇒ `Hom(E(F_p), E(F_n)) = 0`. There is no
> nontrivial **group homomorphism** between the two point groups.

**Why this is NOT a wall for the amicable transfer question:**
1. A DLP reduction is an **algorithm**, not a group homomorphism; coprime-order says nothing
   about a computational shortcut.
2. It is arguably a **strawman**: the standard DLP transfers are not homs `E(F_p)→E(F_n)` —
   MOV maps to `F_{p^k}^*` (blocked by embedding degree), anomalous needs `#E=p` (false),
   Weil descent needs an extension field (secp is prime). I walled a door no one proposed.
3. The **actual** amicable structure — the CM relation `π_n = π_p − 1` in `ℤ[ω]` — is **not
   analyzed**. Whether it yields any reduction is untouched.

**Honest observation (not a proof):** the partner `E(F_n)` has prime order `p ≈ 2²⁵⁶`, so its
DLP is comparably hard — a transfer would trade one hard problem for another. Heuristic
reason the line looks unpromising; **not** a proof no shortcut exists.

**Line 2 status:** one narrow sub-case (abstract group homs) rigorously ruled out; the
general amicable-transfer question (does the CM/Frobenius relation reduce anything) remains an
**open fence**, not a wall. Prior statistical `eis_p`-vs-`eis_n` probes found it generic, but
that too is a scoped null, not an impossibility proof.

## Line 3 — GLV scalar lattice / S₅ rung: no new lever

- **GLV `(a,b)`** (`d ≡ a+bλ mod n`) is a deterministic lattice **re-encoding** of `d`. A
  readout vs `(a,b)` = a readout vs `d` (tested = generic). Recovering `(a,b)` from `[d]G`
  **is** the DLP. No lever from re-encoding.
- **S₅ (4-point decomposition)** confirms the S₄ pattern one rung up: yield/heuristic ≈ 1.0
  for CM and non-CM, β-inv/random ≈ 1.0 (p=1009, 4021). The symmetry lever stays absent, and
  decomposition density stays at the heuristic, up the summation-polynomial ladder.

## Net

All three un-ruled-out lines investigated; none yields a lever. Line 2 rigorously walled only
a **narrow sub-case** (abstract group homs between the point groups) — not the amicable
transfer question itself, which stays an open fence. Nothing here is a proof that ECDLP is
hard; these are scoped nulls and one narrow theorem.
The picture from the whole session holds: the exploitable structure is CM/GLV, capped at
`|Aut|=6`, and every rung of the actual attack surface (relations, 3-pt and 4-pt
decomposition, target selection, amicable transfer) sits at the generic scale.

**Still genuinely un-probed** (not ruled out, mindset = investigate): the **non-homomorphic**
amicable map (only stats + the hom no-go done); everything at **secp's actual p** (all
scaling here is small-to-moderate p); and objects requiring heavy machinery
(explicit S₅⁺ Gröbner/resolution structure rather than yield counting). These are the honest
remaining fence, not walls.
