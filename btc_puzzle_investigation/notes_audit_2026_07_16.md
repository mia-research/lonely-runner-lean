# Audit of the pasted "lift-geometry / frame-operator" notes (2026-07-16)

The notes are from a session that **pre-dates this session's Cap Law proof**. Checked every
item against what is now established. **All explored; two open geometric flags settled
exactly here.** The headline theme of the notes — hunting an *arithmetic* description of ε /
the frame operator — is chasing a seam in objects this session **proved carry no arithmetic**
(they are functions of the lift coefficients `(u,v)` only; `masked_structure_findings_v4.md`
R2/R5). That is closure **by proof**, not by declaration.

## Two open flags from the notes, settled exactly (full lattice enumeration)

| quantity | notes' claim | exact result |
|---|---|---|
| μ₃-core = area(P∩ωP∩ω²P) | "θ-dependent, 3/4→1/2, needs formula" | **3/4 exactly, θ-independent** (p=1009..100003). Their variation = the vertex-ordering bug they flagged. |
| flap density under ω vs ω² | "dichotomy — 3/4:1/8:1/8 only for ζ=ω" | **1/4 either way.** The ζ choice is associate-selection bookkeeping; affects no density. |

Both consistent with the Cap Law (shape constants, θ-independent, inert).

## Item-by-item status

| # | notes item | status | grade / where |
|---|---|---|---|
| 1 | Palelei frame operator: flap λmax/Tr≈0.95–0.97, flaps aligned on R | **explored + PROVED INERT** | flap 33/34=0.9706, axis = long diagonal = R; pure lattice geometry, zero arithmetic. `findings_v2/v4`, `cap_law` memory. Their "core 0.71–0.76" ≠ exact core **1/2** — they used the 97%-proxy norm split, not the exact ε. |
| 2 | θ-closed form: flap sextant {2,5}→{1,4} with θ | **explored** | the rhombus rotates rigidly with θ=arg(π_p); cap sextant labels rotate with it; shape constants θ-independent. Cap Law. |
| 3 | ε 97% norm-determined; "geometric not arithmetic"; χ₆ uniform | **superseded (sharpened)** | ε = `|u+v|>½` **exactly** (linear threshold); norm is the 97% proxy (mixed band 3/16–1/4). "geometric not arithmetic" = the proved **inert lens**. χ₆ uniform ✓. |
| 4 | ζ=ω vs ω² cocycle dichotomy | **checked here** | density invariant (above); GLV μ₃ action handled in `findings_v6` (the exact GLV zero). Bookkeeping, not structure. |
| 5 | area P∩ωP=3/4; μ₃-core θ-dependent | **checked here** | P∩ωP=3/4 ✓; μ₃-core=3/4 exactly, θ-independent (refutes the θ-dependence). |
| 6 | Avenue 1: three-point lift eis(x(P+Q)) vs sum | **explored** | 2-pt β-relation PROVED (`eis(βX)=ζ·eis(X)+{0,±R}`, `glv_2point_lift_law`); general P+Q spread/generic (`addition_lift`); difference-set bilinear built & powered-generic (`findings_v6`). |
| 7 | Avenue 2: ε(d) vs χ₆(d), d mod 6, D-sig | **covered / forbidden** | ε has small Wiener norm ⇒ closure-covered vs additive d-features (generic); scalar-mult ψ(d) tested generic (`findings_v5`). D-sig part = generation-side (forbidden). |
| 8 | Avenue 3: formal-group valuation v_p(T_d) vs norm | **explored (trivial)** | `glv_formal_param_valuation_probe`: on reduced points T_d is a unit ⇒ v_p≡0; entry map = DLP. |
| 9 | Avenue 4: amicable 2-cycle = spectral fixed point | **resolved NEGATIVE** | `amicable_spectral_fixedpoint`: NOT spectral; it is a **Frobenius** fixed point (1−π)−1=−π. Tested, controlled. |
| 10 | Avenue 5: D-signature additive+mult residue | **forbidden + already null** | generation-side (`feedback_no_prng`); and `dsig_residue_eval`: real≡random χ²=2.4, "μ₆ core" REFUTED = denominator artifact; D-sig = Engel artifact. |
| 11 | Avenue 6: rank-10 matrix μ₃-split | **explored** | `handover_int_panels` Int.2: rank-10 is μ₆-ROBUST, no decomposition. |

## Bottom line

Nothing in the notes is unexplored. The frame-operator anisotropy, the flap alignment, the
ε-norm determination, and the sextant-θ pattern — presented there as "the deepest structural
insight" and "novel" — are the **Cap Law shape constants this session proved are inert**
(they carry no arithmetic; every downstream density is a fixed rhombus constant). The
avenues are either covered-and-generic, resolved-negative, or generation-side/forbidden.

The redirect (where live arithmetic actually is, per `findings_v4–v6`): **not** in any ε /
norm / frame / sextant readout (proved shape-determined), but in (a) the distribution of the
map `x↦(u,v)` itself — its joint 2-D/higher structure over key sets, at secp's p; (b) the
difference set on **finer statistics** than flap/S3 (additive-energy/collision counts);
(c) odd probes **quotiented by the GLV μ₃ action**. Those are the objects not yet exhausted.
