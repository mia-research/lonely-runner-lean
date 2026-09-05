# Addition-lift law + two-domain residue — findings (v1, 2026-07-14)

Companion to `POSITIVE_FINDINGS_HANDOVER_2_v1.md` (the lift-geometry launching pad).
This session attacked the one operation the Eisenstein lift does **not** already
linearize: point **addition** (= the DLP-bearing operation), in both the
coordinate frame (π_p) and the two-domain scalar frame (π_n), following the plan
in Handover-2 §5/§6. All arithmetic exact (`int`/`Fraction`) in the
point/lift/label path; float only in MI/z rank statistics vs a matched
permutation null. Every result below is **EMPIRICAL, scoped** — bound to the
labels / sample size / bridge stated — **not closure**.

## Scripts
- `glv_addition_lift_conditioned_v1.py` — point-addition law, CONDITIONED on CM labels.
- `glv_two_domain_residue_v1.py` → `_v2.py` — two-domain residue vs the amicable
  slippage bridge (v1 retracted for a tautology; v2 is the corrected object).
- `glv_addition_eps_reprobe_v1.py` — large-N settle of the one non-flat reading.

## 1. Point-addition law in the coordinate (π_p) frame — CONDITIONED
For independent random points P, Q with S = P ⊕ Q, lift x_P, x_Q, x_S and test
whether any cheap CM label L(·) is a homomorphism, L(S) predicted by (L(P),L(Q)):

- **sextant (Z/6):** MI **halves each doubling of N** (0.0129→0.0056→0.0027), z
  collapses (+2.4→+0.4). Textbook `MI~1/N` noise; the small-N z is the sample echo.
  **No sextant homomorphism.**
- **norm-band {0,1,2}:** z goes negative (−0.2→−1.1). Noise.
- **naive additive correction** `c3 = reduce_P(U_S − U_P − U_Q)`: fully spread
  (M/M distinct, top-mass 1/M) and stays spread inside **every** (ε_P,ε_Q) and
  (s_P,s_Q) cell (the small cells' higher top-mass is just 1/cellsize). Addition
  does **not** linearize in the π_p coordinate lift even conditioned on CM labels.
  (Caveat: `U_S − U_P − U_Q` is the *wrong* baseline — the group law is
  `x_S = λ² − x_P − x_Q`, not additive on x. See §4.)
- **ε (μ₃-orbit label {0,+,−}):** the single non-flat reading. Re-probed to
  N=180k: MI **plateaus ~0.00012 bit** while the null floor falls ~1/N, so
  z climbs −1.66→−0.38→+0.47→**+2.42** (control −0.41, clean). Read: a **faint,
  suggestive-not-decisive residual dependence**, magnitude ~0.0001 bit out of
  ε_S's ~1.06-bit entropy — ε_S keeps ~all its entropy given (ε_P,ε_Q). **ε is
  NOT a homomorphism under ⊕.** A faint residual is *expected* (x_S is a group-law
  function of x_P,x_Q, so their geometric labels are not independent); it is far
  too small to be a handle. Confirmed on curve points: ε marginal = **0.7500 :
  0.1285 : 0.1216** ≈ the single-point 3/4:1/8:1/8 law.

## 2. Two-domain residue vs the amicable slippage bridge — CORRECTED (v2)
Both p and n split in ℤ[ω]: coordinates live in ℤ[ω]/(π_p)=𝔽_p (lift `eis_p`),
scalars in ℤ[ω]/(π_n)=𝔽_n (lift `eis_n`), π_n = π_p−1. Confirmed slippage
`R1_p−R1_n=(0,1)`, `R2_p−R2_n=(1,1)` (Handover-2 §4). For known-d samples,
`w = eis_n(d)`, `v = eis_p(x([d]G))`, `Mw` = w's π_n-basis coords re-embedded in
the π_p basis; residue `r = v − Mw`.

**Retraction (v1):** v1 correlated `sextant(r)` against `sextant(w)` and got
`MI=0.48–0.64 bit, z=+5000`. This is a **tautology**, not a break: `r` is built
from `w`, so their angles co-vary as a pure subtraction artifact even for
independent v,w; the shuffle-control passes (→0) because shuffling breaks the
artifact just as it would break real signal — the passing control *masks* it.
Recorded as a reusable failure mode (`feedback_residue_vs_component_tautology`).

**v2 (correct object) — boundedness + non-circular leakage, N=90k:**
- **r fills P_p:** distinct(r)=90000/90000, top-mass=1/M, N(r) median bit-length
  257. The coordinate map is **not** linear-up-to-bounded-wrap against the
  amicable bridge; the DLP scramble is total at this level.
- **non-circular leakage** (feature and target of disjoint construction), all
  with clean controls (z≈−0.5 to −0.8):
  - `sextant(v)` vs `sextant(w)` (coord angle vs scalar angle): z −0.4/−0.2/+0.1.
    Resolves the v1 mild z~1.8 as small-sample. **Null.**
  - `eps(v)` vs `d mod 6`: z −0.2/+0.2/−0.2. **Null.**
  - `sextant(v)` vs `d mod 6`: z −0.9/−0.5/+0.8. **Null.**

This is **sharper** than Handover-2 §5's coarse-grid MI (we formed the exact
algebraic residue against the known bridge and checked boundedness directly), and
it is a **scoped exact-residue result**: at these labels / N=90k / this bridge,
the two-domain coordinate map shows no residual linearity and no d-leak. It says
this **panel** (linear coordinate map in the two-domain lift) is not the gate —
**not** that the coordinate map has no structure.

## 3. Fence-map update
- **Multiplicative side** (single-x lift readouts, the endomorphism cocycle): the
  hypothesis that these are d-blind remains a hypothesis with scoped-null support
  — **not a proved panel**. Upgrading it to a Weil/Kohel–Shparlinski theorem is
  still the clean "prove a panel solid" move.
- **Addition side, π_p frame:** no cheap-label homomorphism (sextant/norm noise;
  ε not homomorphic, faint expected residual). Scoped, not closure.
- **Two-domain linear bridge:** residue uniform, no linearization. Scoped panel.

## 4. What this points at next (not yet done)
The naive additive baseline `U_S − U_P − U_Q` is the *wrong* object: the true
group-law constraint is the **third summation polynomial** `S₃(x_P,x_Q,x_S)=0`,
which is already known to be **[ω]-covariant** (eigenvalue β¹; Handover-3 Part II).
The correct "addition lift law" test is whether the lift of the `S₃=0` relation
variety concentrates when conditioned on the CM labels — the group law expressed
as its actual (nonlinear, CM-covariant) constraint, not an additive approximation.
That is the untested object the two experiments here clear the way to.
