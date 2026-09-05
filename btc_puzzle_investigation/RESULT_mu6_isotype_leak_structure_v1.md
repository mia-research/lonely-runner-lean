# μ6-isotype grading of readouts — tying the flap-null to the leak-structure

Date: 2026-07-18. Follows [RESULT_glm_flap_arithmetic_test_v1.md]. Object: Aut(E)=μ6 acting
on the scalar d (via GLV d↦λd, λ²+λ+1≡0 mod n, and negation d↦−d), linked to the μ6 on the
x-coordinate (x_{λd}=βx_d) that the flap ε is invariant under.
Model curve (exact d-enumeration): E: y²=x³+**7** over F_2143, prime order n=2089≡1 mod3,
β=1793 mod q, λ=1262 mod n. Script `scratchpad/mu6_isotype.py`.

## Verified exactly (integer/label equality; no float in the structural claims)
- **Transformation identities:** x_{λd}=βx_d, y_{λd}=y_d, x_{−d}=x_d, y_{−d}=−y_d. [PROVED — algebraic, holds for any j=0 curve incl. secp256k1.]
- **ε is the trivial isotype (0,+) in d:** ε(λd)=ε(d) AND ε(−d)=ε(d) for all d. [Follows: ε(x_{−d})=ε(x_d) trivially since x_{−d}=x_d; ε(x_{λd})=ε(βx_d)=ε(x_d) uses ε's proven μ3-invariance. Verified on the model curve; ε's μ6-invariance separately verified at primes 10⁵–10⁶.]
- **μ6-types (w mod3, parity s):** x=(1,+), y=(0,−), xy=(1,−), x²=(2,+), y²=(0,+), ε=(0,+). [x,y from the identities; monomials by multiplicativity.]
- **Cross-isotype orthogonality (Schur):** ⟨ε,y⟩=0 exactly (ε even × y odd, pairing d↔−d). Two readouts of different (w,s) are orthogonal as functions of d.
- **ε is blind to the sign of d:** Σ_d ε(d)[e_n(ad)−e_n(−ad)]=0 exactly, for every a (ε even, bracket odd). A parity-odd readout (sign y_d) gives a nonzero odd-projection — it DOES carry the sign of d.

## What this explains
The character-null of the flap (`RESULT_glm_flap_arithmetic_test_v1`: ε ⊥ χ2/χ3/χ6, χ²=0 exact)
and the flap's geometry-only content are one fact seen through Aut(E)=μ6: **ε lives in the trivial
isotype, so it is orthogonal to every readout that separates d, λd, or −d — which is exactly what a
DLP character e_n(a₀d) does.** The parity (Z/2) half of this is generic (any function of x alone is
parity-even in d, since x_{−d}=x_d); the μ3-weight-0 half is the CM/GLV structure. This is precisely
GLM's even/odd Fourier observation (correct in spirit) refined by the CM μ3-grading it lacked.

## Scope / caveats (baked in so the artifact does not overreach)
- **NOT a reproduction of the 0.93 leak.** Only the qualitative isotype structure + exact
  orthogonality are shown — where d-information must live, not a magnitude match.
- **The μ3-weight grading is prior work** (master: "xy = odd-in-d + μ3-weight-1"). New here: placing
  ε in it (trivial isotype), the exact cross-isotype orthogonality, and the sharp μ6 group.
- **"Leak lives in nontrivial isotypes" is not a lever.** The d-carrying readouts are exactly those
  whose cheap evaluation would BE the DLP; the grading organizes/explains the null, it does not extract.
- ε being μ3-weight-0 is nearly by-construction (ε is a μ3-orbit label). The non-obvious facts remain
  χ²=0 exact and μ6 sharp.
- One model curve for the d-enumeration (n=2089). Identities are algebraic (curve-independent);
  secp256k1 d-indexed readouts not enumerated (2²⁵⁶).

## Where the structure goes next (decidable, not closures)
1. **μ6-equivariance of the bilinear leak spectrum — VERIFIED EXACT.** U(a,b)=Σ_d e_q(b·x_d) e_n(a·d)
   satisfies **U(a,b)=U(λa,βb) exactly** (reindex d↦λd: x_{λd}=βx_d, e_n(a·λd)=e_n(λa·d)) and
   U(−a,−b)=conj U(a,b). Checked 0.00e+00 on the model curve. So the leak spectrum is constant on the
   μ6-orbits of the (a,b)-torus under the DIAGONAL action (a,b)↦(λa,βb) and (a,b)↦(−a,−b) — a ~6-fold
   fundamental domain. This is the two-sided version, directly the KS/masked-structure U(a,b,·) object:
   the isotype grading on d and the field-frequency grading on b are the SAME μ6. Next: quantify how
   much the μ6 fundamental domain shrinks the independent spectrum, and whether any KS-corner sits at a
   μ6-fixed point of the torus (the only places the equivariance does not reduce the count).
2. **A μ3-weight ceiling beyond the parity ceiling.** GLM's even/odd ceiling is the Z/2 isotype; does
   the μ3-weight refinement impose a SHARPER bound on a cheap readout's alignment with e_n(a₀d) than
   parity alone? Reconnects to the aligned-leak scaling.
3. **CM-type dependence (j=1728, Aut=μ4).** Predicts a flap ⊥ χ4,χ2 but NOT χ3 — tests "Aut(E)
   fixes the character-orthogonality group" across CM discriminants. Needs a Gaussian-integer lift.
