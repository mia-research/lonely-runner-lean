# PREREG v1 — the [ω]-twisted Lefschetz probe of "geometric μ₃" behind the 120° law

**Date:** 2026-08-21. **Status: SPEC ONLY — no confirmatory sweep computed.** This file freezes the
statistic, the matched/planted controls, power, scope, and falsification for the D-mechanism
(geometric μ₃) BEFORE any sweep over a≠0 cells or over primes. Nothing runs until this file is frozen
(SHA-256 alongside) and the frame gate returns on *this* file.

**SCOPE BANNER (binding).** Output is a STRUCTURAL characterization only: does the CM endomorphism
[ω] act GEOMETRICALLY on the fibre H¹_c(F_a), and would that force uniformity of ρ(a)=α₂/α₁=ζ₃ over
a≠0. This is a statement about eigenvalue / cohomology structure. It MUST NEVER be reported as, or
bridged to, scalar extraction, "carry bounds," key recovery, or any ECDLP / security consequence. The
map from eigenvalue/cohomology structure to any scalar `d` is a separate, unbuilt object and is
explicitly OUT OF SCOPE here. No leakage / key-recovery / ECDLP claim is made or licensed.

**Grade slot: `[PRE-REGISTERED — HOLD; statistic fails the OBJECT/tautology gate at a≠0, §2 + §9].`**
The confirmatory sweep over a≠0 is **NOT authorized by this spec** — for three decidable, pre-data
reasons (§2). The D-mechanism (that μ₃ acts geometrically / that ρ is uniform) is **OPEN and is not
refuted**; what this spec establishes is that the *proposed twisted-Lefschetz statistic* is not an
object-level test of the VERTICAL mechanism at a≠0. Its correct object-level probe is named in §9.

Grades used: `[PROVED]` exact identity all p in class; `[REPRODUCED-exact]` exact, finite sample as
stated; `[CITED]` external; `[OPEN]` not shown; `[FORCED]` algebraically forced ⇒ zero information.

---

## 1. OBJECT

`p` prime, `p ≡ 7 mod 12` (⊇ secp; forces ω=ζ₃∈F_p, p≡3 mod 4); `E: y²=x³+7`; `n=#E(F_p)`. For
`a∈(ℤ/N)*` the rank-4 sheaf `F_a = L_{χ₂(y)} ⊗ L_{χ_a}` on `E` minus its tame points; `dim H¹_c=4`;
Frobenius eigenvalues `α_i(a)`, Weil weight 1 (`|α_i|=√p`). Statistic of record (established, elsewhere):
the within-pair ratio `ρ(a)=α₂(a)/α₁(a)`; the "120° law" is `ρ(a)=ζ₃`, equivalently
`g(a)=deg gcd(L*_a(T),L*_a(ζ₃T))=2`. Power sums `p_k(a)=Σα_i^k=−V_k(a)`, with the EXACT point-count
`V_k(a)=Σ_{P∈E(F_{p^k})} χ₂(y_P) χ_a(Tr_{k/1}P)` (Grothendieck–Lefschetz trace formula).

**Neutral established facts (given; not re-derived here).**
- (Anchor a=0) `[PROVED]` `A_new` (the a=0 untwisted supersingular fibre) has multiset
  `√p·{ω,ω²,−ω,−ω²}` (ζ₂₄ exponents {4,8,16,20}, orders [6,3,3,6]); the N1 statistic gives g=2. `0∉(ℤ/N)*`,
  so this fibre is OUTSIDE the open quantifier.
- (Per-cell law) `[REPRODUCED-exact, p≤211, all cells]` multiset `{α,ζ₃α,−ᾱ,−ζ̄₃ᾱ}`, g=2.
- (ω-descent) `[PROVED]` `V_k(a)=V_k(λa)` ∀k, so `L*_a = L*_{λa} = L*_{λ²a}` as polynomials, where
  λ∈(ℤ/N)* has order 3 (= the action of the CM endomorphism [ω]:(x,y)↦(ωx,y) on E(F_p)≅ℤ/N).
- (Horizontal, not vertical) `[PROVED — obstruction analysis §3]` `[ω]^*: H¹_c(F_a) →~ H¹_c(F_{λ²a})`
  is a Frobenius-equivariant **isomorphism, not an endomorphism** of the fibre for a≠0 (it is an
  endomorphism iff λa=a iff a=0). Under the twist a=0→a≠0 the ABSOLUTE rigidity (each α_i=√p×root of
  unity) is DESTROYED (Sato–Tate equidistribution); only the RELATIVE ratio ρ is the candidate invariant.
- (No eigenvalue statistic separates geometric from formal) `[PROVED — jclass §0.1]` a multiset of
  shape W⊔ζ₃W is compatible with a non-split extension; traces see only the semisimplification; the
  operator-`T` test (`T·Frob=ζ₃·Frob·T`) is CIRCULAR and was RETIRED, not deferred.

**OPEN quantifier (the target):** `ρ(a)=ζ₃` for ALL `a∈(ℤ/N)*`, ALL `p≡7 mod 12`, to p≈2²⁵⁶.

**D-mechanism (hypothesis to characterize).** The CM endomorphism [ω] acts GEOMETRICALLY (vertically,
within one fibre — not merely by the horizontal fibre permutation a↦λa) on H¹_c(F_a), and this action
forces ρ(a)=ζ₃ uniformly. Candidate probe (as proposed): the twisted Lefschetz
`L_j(m,a) = Σ_i (−1)^i Tr([ω]^j∘Frob^m | H^i_c(F_a))`, `j∈{0,1,2}`, `m≥1`, by exact point-counting.

**★ OBJECT-level tautology / ill-posedness flag (this is the finding; see §2 for the decidable form).**
The feature ("[ω] acts as an endomorphism of the fibre realizing the ζ₃ ratio") and the target
("ρ(a)=ζ₃") share construction. For a≠0, j∈{1,2}, `[ω]^j∘Frob^m` maps `H^i_c(F_a) → H^i_c(F_{λ^j a})`
with `λ^j a ≠ a`; it is **not an endomorphism of the fibre**, so `Tr(…|H^i_c(F_a))` is not defined
without an extra datum. Supplying that datum, or reading it off the semisimplification, reproduces the
census statistic. Per the OBJECT rule, this must be stated before the run: the twisted-Lefschetz trace
is not an object-level, non-circular test of the VERTICAL mechanism at a≠0.

---

## 2. STATISTIC (exactly one) and its distribution under the correct null

Statistic: the [ω]-twisted Lefschetz number `L_j(m,a)` above, aimed at the predicted μ₃ subspace
splitting. Under the geometric-μ₃ hypothesis the prediction is `L_j(m,a) = Σ_i θ_i^j α_i(a)^m` with
`θ_i∈μ₃` the [ω]-eigenspace assignment on the four eigenlines; the "geometric" branch requires the
assignment that pairs α₂=ζ₃·α₁ (i.e. θ₂=ζ₃·θ₁ on that line). The verdict was to be match-vs-mismatch
of exact integer counts. **Three decidable facts, all pre-data, determine that this statistic cannot
render that verdict at a≠0:**

**(R1) On the correct MATCHED null — the orbit-summed object — L_j is a FORCED ZERO for j∈{1,2}.**
The only Frobenius-equivariant space on which `[ω]` is a genuine endomorphism (a≠0) is the direct sum
over the λ-orbit, `W_a := H¹_c(F_a) ⊕ H¹_c(F_{λa}) ⊕ H¹_c(F_{λ²a})` (dim 12). There `Θ:=[ω]^*`
cyclically permutes the three summands (Θ³=[ω³]^*=id, since [ω]³=id_E), and each summand carries the
SAME char poly (ω-descent). For j∈{1,2}, `Θ^j` sends every summand off-diagonal (λ^j a≠a), so
> `L_j(m; W_a) = Tr(Θ^j Frob^m | W_a) = Σ_{χ∈μ₃} χ^j · p_m(a) = (Σ_{χ∈μ₃} χ^j)·p_m(a) = 0`,   j∈{1,2},
exactly, for ALL a≠0, ALL p, ALL m — a purely algebraic identity (the μ₃ acts by its regular
representation; twisted traces of the regular rep vanish off the identity). `[FORCED ⇒ zero information]`.
A forced zero carries no information about ρ; a nonzero readout would be measuring a chosen gluing, not
geometry. This is the exact analogue of the logged "6–7σ soft shadow" null-mismatch: a naïve control
that destroys a symmetry the object has by construction. **No sweep is needed to know this value.**

**(R2) On a SINGLE fibre (a≠0), L_j (j∈{1,2}) is ill-defined without a gluing datum that exists only
at a=0; any supplied choice builds in ρ=ζ₃.** The Lefschetz–Verdier trace of the correspondence
`[ω]^j∘Frob^m` on `F_a` requires a sheaf morphism `u: [ω]^{j*}F_a → F_a`, i.e. `F_{λ^j a} → F_a`. Such
`u` exists (canonically, ≅) iff `λ^j a = a` iff `a=0`. For a≠0, j∈{1,2} there is no canonical `u`; any
choice trivializing `F_{λ^j a}≅F_a` is extra data, and the ρ read off the resulting number is that
choice's, not the geometry's. `[TAUTOLOGY — feature shares construction with target]`.

**(R3) The only well-defined single-fibre variant equals the already-RETIRED circular test.** Any
within-fibre operator realizing α₂=ζ₃·α₁ on H¹_c(F_a) has existence equivalent to g(a)≥1 (the census
statistic) and cannot separate a genuine geometric endomorphism from a formal / non-split-extension one
(traces see only the semisimplification, jclass §0.1). `[REDUCES TO the retired operator-T test]`.

**Conclusion of §2 (pre-data):** as a test of the VERTICAL mechanism at a≠0, `L_j(m,a)` is
forced-zero (R1) / ill-defined-without-a-choice (R2) / circular (R3). It IS well-defined and
computable in exactly one regime — the a=0 anchor — where it is a reproduction control (§4), not a
test of the open quantifier.

---

## 3. MATCHED CONTROL

The matched null must reproduce every structure the real fibre has EXCEPT the vertical μ₃ splitting.
The correct such null is the **orbit-summed object `W_a`** of R1: it preserves purity, the Weil
pairing α↦−ᾱ, ω-descent, σ_λ-descent, and the HORIZONTAL μ₃ (fibre permutation, PROVED), and it
"destroys" only the hypothetical vertical within-fibre μ₃ (by symmetrizing over the orbit). Against
this null the twisted trace is the FORCED ZERO of R1 for j∈{1,2}. A shuffle / random-gluing surrogate
is an INVALID null here: it destroys the ω-descent iso the object has by definition (exactly the
logged failure where "the shuffle breaks the artifact as it breaks real signal"), so it cannot expose
the R2 tautology. **State plainly:** the only matched null available is orbit-summing, and against it
the statistic is identically 0 for j∈{1,2} — i.e. the null and any correct computation coincide, so
the statistic has no discriminating content at a≠0.

---

## 4. PLANTED CONTROL

A positive control must inject a KNOWN geometric μ₃ and fire.
- **P-anchor (a=0).** At a=0, `[ω]` IS a genuine endomorphism of H¹_c(F_0)=H¹_c(L_{χ₂(y)}); the
  twisted count `L_j(m,0) = Σ_{P: [ω]^j Frob^m P = P} χ₂(y_P)` is well-defined by exact point-counting.
  Predicted (exact, from the anchor multiset √p·{ω,ω²,−ω,−ω²} with the μ₃-eigenspace assignment θ_i):
  `L_j(m,0) = Σ_i θ_i^j α_i^m`, θ_i∈μ₃; concretely the j=1,2 twisted traces are NONZERO combinations
  of the ζ₂₄-power eigenvalues (the assignment is derived by exact reduction in ℤ[x]/Φ₂₄, not asserted).
  This control **fires** (μ₃ is genuinely geometric at a=0). **But it fires only in the regime that is
  NOT the object of interest** (a=0 ∉ open quantifier). So the plant firing does NOT license any a≠0
  conclusion; it is a consistency/reproduction control only.
- **⇒ The null is uninformative for the target.** By the standing rule "a planted control that fires
  only outside the object's regime, while the matched null in the object's regime is a forced zero,
  cannot validate an a≠0 verdict." There is no plant that fires INSIDE the a≠0 regime without
  presupposing the gluing of R2, i.e. without being the tautology. **This is the decisive reason the
  a≠0 sweep is held (§9).**

---

## 5. POWER

- For the OPEN quantifier (ρ uniform over a≠0): the twisted-Lefschetz statistic has **ZERO power** —
  it is forced-zero (R1), ill-defined (R2), or circular (R3). No `n`, no prime schedule, no cell count
  yields a decisive non-circular match/mismatch on ρ(a)=ζ₃ for a≠0. (This mirrors the logged
  zero-power null where N=82 needed effect size f=1.0 to detect anything.)
- For the a=0 anchor: the "match" is a FORCED algebraic identity (the anchor multiset is forced for all
  p≡7 mod 12 by the m-law); reproducing it across primes is a derivation, not evidence — zero
  statistical content, however many primes are swept.
- Reachable p for EXACT computation (recorded for completeness): full H^i_c point-counts on `E` and on
  the μ₃/μ₆ covers are exact by integer point enumeration over F_{p^k} for `k≤6` at **p ≲ 10³–10⁴**
  (cost ~p^k); secp's p only for the a=0 anchor consistency (already established), never for an a≠0
  point-count. None of this converts zero power on the open quantifier into positive power.

---

## 6. SCOPE

Model curves `E: y²=x³+7` (and the cubic/sextic covers) at moderate p (p≲10³–10⁴) for any a=0 anchor /
cover computation; secp's own p ONLY for the a=0 anchor consistency check (already established
elsewhere). Primes p≡7 mod 12, cubic-non-residue arm (B=7), with the cubic-RESIDUE arm as the negative
control (§7). j∈{0,1728, generic} curves as the automorphism-group discriminators (§7). Any number this
design could produce inherits: "a=0 anchor, forced identity" or "orbit-summed, forced zero" — and may
never be stated as an a≠0 uniformity result. **No ECDLP / scalar / key-recovery reading (SCOPE BANNER).**

---

## 7. NEGATIVE / DISCRIMINATING CONTROLS (and their true reach)

All are well-defined only in the a=0 anchor / geometric-cover regime, where they DO discriminate the
HORIZONTAL μ₃ structure. State that they bear on the horizontal (already-PROVED) claim, NOT on the
open vertical uniformity.

- **m=−2 branch (cubic-RESIDUE case).** Anchor multiset `√p·{1,1,−1,−1}` (m=−2), orders [1,1,2,2],
  g=0 — no ζ₃ ratio. Prediction: the [ω]-twisted anchor count shows NO μ₃ eigenspace splitting
  (θ_i∈{±1}, the μ₃-twisted traces L_1,L_2 collapse to the ordinary L_0 pattern). MUST behave so, or
  no verdict. Discriminates the cubic-residue symbol at the ANCHOR; says nothing about a≠0.
- **j=1728 curve (CM by ℤ[i], μ₄ not μ₃).** `y²=x³+Ax`; here `[ω]` is not an automorphism (Aut=μ₄),
  so the [ω]-twist is structurally ABSENT/degenerate. Prediction: L_j for a μ₃-twist is undefined /
  trivial; the μ₄-twist is the live one (cf. the recorded μ₄ eigenvalue law). Also note the recorded
  structural fact: j=1728 can never have prime order (2-torsion (0,0)), so it never matches the
  cofactor-1 secp setting — the arm exists only as a μ₄-vs-μ₃ automorphism discriminator.
- **a=0 anchor reproduction.** Exact reproduction of `√p·{ω,ω²,−ω,−ω²}`, g=2, and the well-defined
  L_j(m,0) of §4 — the P-anchor plant. MUST reproduce, or the pipeline is not trustworthy.

**All three fire in the horizontal / anchor regime and confirm the automorphism-group structure that
ω-descent already PROVES. None of them provides an a≠0 vertical verdict.**

---

## 8. EXACTNESS

Exact signal path throughout: all point counts exact over GF(p) (integer enumeration; no float); ζ₃
and root-of-unity membership by exact reduction in ℤ[x]/Φ_k (k∈{3,6,24}), never asserted from a numeric
root-finder; g and any resultant computed exactly in ℤ[x]/(Φ_N,Φ_k). No float threshold decides any
verdict. Anchor multiset and the θ_i assignment are DERIVED by exact reduction in ℤ[x]/Φ₂₄, per the
standing rule that a pasted root system in this slot was previously wrong. No float carve-out is needed;
none is taken.

---

## 9. PRE-COMMITMENT (filled BEFORE the run) + FALSIFICATION

**Pre-committed conclusion for each possible outcome — decided now, before any sweep:**

| regime / arm | what the statistic yields | pre-committed conclusion |
|---|---|---|
| a≠0, j∈{1,2}, orbit-summed (matched null, R1) | L_j = 0 exactly, ∀a,∀p,∀m `[FORCED]` | no information on ρ; NOT a test of the vertical mechanism |
| a≠0, j∈{1,2}, single fibre (R2) | undefined without gluing u; any u builds in ρ | invalid before it runs (tautology); do not compute as a verdict |
| a≠0, single-fibre operator realizing α₂=ζ₃α₁ (R3) | = census g(a)≥1; can't separate geometric/formal | reduces to the RETIRED operator-T test; no new content |
| a=0 anchor, j∈{1,2} (P-anchor plant) | L_j(m,0)=Σθ_i^j α_i^m, nonzero, exact | control FIRES; reproduction only; a=0 ∉ open quantifier |
| m=−2 anchor / j=1728 arm (§7) | no μ₃ splitting / μ₃-twist degenerate | discriminates HORIZONTAL structure only |

**⇒ Pre-committed overall verdict: HOLD.** The confirmatory a≠0 sweep is **not authorized** by this
spec, because the statistic fails the OBJECT/tautology gate at a≠0 (R1 forced-zero, R2 ill-posed, R3
circular) and no plant fires inside the a≠0 regime without presupposing the answer (§4). This is a
statement about the TEST, graded and scoped; it does **not** refute the D-mechanism. The vertical
geometric-μ₃ mechanism, and uniformity of ρ over a≠0, remain **`[OPEN]`**.

**FALSIFICATION (of the *statistic's* adequacy — decided pre-run):** the statistic is declared
inadequate for the vertical mechanism iff ANY of: (i) the orbit-summed L_j (j∈{1,2}) is not a forced
zero — it is (R1 is an identity), so this is settled; (ii) a single-fibre L_j at a≠0 requires a choice
of gluing — it does (R2); (iii) the single-fibre operator test coincides with the retired census
statistic — it does (R3). All three hold pre-data ⇒ the statistic is inadequate ⇒ HOLD. Conversely,
the statistic would be RE-ADMITTED only if a matched null were exhibited on which some L_j (j≠0, a≠0)
is UNFORCED and NON-circular; none is known.

**FALSIFICATION (of the D-mechanism, for a *future* valid probe):** the D-mechanism would be refuted if
the correct vertical object (below) exhibits an a≠0 orbit representative with ρ≠ζ₃, or shows the
unit-root part carries NO CM by a field containing ℚ(ω); it would be supported if that CM/Hecke input
is present and p-independent. Both are positive results (support = evidence toward the uniformity
mechanism; refutation = an informative redirect), reported with power+scope, no dismissal vocabulary.

**The correct object-level vertical probe (redirect, not a closure).** Per the obstruction analysis §4,
the vertical mechanism is a CM-type Hecke input, testable NOT by a point-count trace but by: (CM-i) does
the ordinary unit-root part (Newton slopes {0,0}) of H¹_c(F_a) carry CM by an order in a field ⊇ℚ(ω);
(CM-ii) is its Frobenius a value of a Hecke Grössencharacter ψ (infinity-type + conductor, data
independent of p) twisted by χ_a; (CM-iii) does the CM-type force α₂=ω·α₁ at every split prime 𝔭 at
once. That is a Grössencharacter / infinity-type computation, a different object from the twisted
Lefschetz, and is where a valid uniformity test lives. It is left to a separate, pre-registered spec.

---

## 10. Freeze / deviations

Freeze = SHA-256 of this file (in `PREREG_omega_twisted_lefschetz_120deg_v1.md.sha256`). Any departure
from this spec is logged in `PREREG_omega_twisted_lefschetz_120deg_v1_DEVIATIONS.md`, opened at freeze.
No sweep is run under this spec (verdict = HOLD, §9).
