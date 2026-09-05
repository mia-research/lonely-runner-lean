# LENS NOTE — Bridge ↔ 120° link: literature review & honest assessment (v1)

**Mode:** INVESTIGATION (lens-open). **Date:** 2026-07-30.
**Question.** Is the $\mu_3$ of the proved cubic bridge ($\chi_3(p\bmod n)=\omega^{c_3}\chi_3(n\bmod p)$,
a residue-symbol identity in $\mathbb{Z}[\omega]$) the same group element as the $\mu_3$ of the
120° law ($\alpha_2/\alpha_1 = \zeta_3$, a Frobenius-eigenvalue-ratio identity on $H^1_c$)?
The lens predicts yes. This note records what the literature says.

This is private lens-led investigation in `.zcode/notes/`. It is not a project artifact.

---

## Verdict

**The link is structurally motivated but NOT a known theorem.** No paper directly states
"the bridge's $\mu_3$ = the eigenvalue-ratio $\mu_3$ as the same $G_{\text{geom}}$ element."
What the literature does provide is a through-line of three independent results that *point
at the same connection* without drawing it explicitly. The lens prediction is therefore
**novel** (not a rediscovery), and **tractable to attempt** along the path below, but a real
proof still requires identifying $G_{\text{geom}}$ (Frontier #28).

## The three-pointed through-line

### 1. Matthews 1979 — the Kummer sum IS a CM elliptic function value
**C.R. Matthews, "Gauss Sums and Elliptic Functions. I. The Kummer Sum," *Invent. Math.* 52
(1979), 163–186.** ([eudml](https://eudml.org/doc/142647))

The cubic Gauss sum (Kummer sum) for $p\equiv 1\bmod 3$ lives in $\mathbb{Z}[\omega]$
([Wikipedia: Kummer sum](https://en.wikipedia.org/wiki/Kummer_sum)). Matthews expresses it
**in terms of CM elliptic function values** — i.e. the algebraic object the bridge is built
from (a cubic-residue / Gauss-sum identity in $\mathbb{Z}[\omega]$) is *the same* algebraic
object as a CM elliptic function value. This is the algebraic bridge from the
reciprocity/residue side to the CM-elliptic-curve side.

`[LENS]` This is the structural reason the lens predicts the two $\mu_3$'s coincide: both
objects factor through the same CM elliptic function / $\mathbb{Z}[\omega]$ arithmetic, so
the $\mu_3$ acting on one *should* be the $\mu_3$ acting on the other.

### 2. The Fermat-curve embedding criterion — eigenvalue-ratio-is-root-of-unity is structural
**MathOverflow: "Does every CM elliptic curve occur inside the Jacobian of a Fermat curve?"**
([MO 512660](https://mathoverflow.net/questions/512660))

The answer (paraphrased): a CM elliptic curve $E$ is a direct summand of the Jacobian of the
Fermat curve $X_m$ iff its Frobenius eigenvalues match those of $X_m$ **up to multiplication
by a root of unity**. For discriminant $-3$ (i.e. $j=0$, our case), this *holds* in $X_3$ —
"the CM elliptic curves of discriminant $-3$ occur inside $X_3$."

`[LENS]` This is exactly the 120°-law structure — Frobenius eigenvalues differing by a root
of unity ($\zeta_3$). The fact that it's *forced* for $j=0 \subset X_3$ gives a structural
reason the eigenvalue ratio is a root of unity: **the $j=0$ curve's Frobenius structure
embeds into the Fermat cubic, whose Jacobian carries a natural $\mu_3$.** The $\mu_3$ is the
Fermat curve's, inherited by the embedded summand.

### 3. Katz AM-180 — the framework, but not the link
**N.M. Katz, *Convolution and Equidistribution: Sato–Tate Theorems for Finite-Field Mellin
Transforms* (AM-180, 2012).** ([Princeton PDF](https://web.math.princeton.edu/~nmk/mellin324book.pdf),
[DeGruyter](https://www.degruyterbrill.com/document/doi/10.1515/9781400842704/html))

Katz's framework is *the* natural home for $V(a)$ (the finite-field Mellin transform of
$\chi_2(y_P)$ on $E(\mathbb{F}_p)$) and attaches $G_{\text{geom}}$ whose trace distribution
the values follow. **But Katz's theorems as black boxes give equidistribution, not the
pointwise eigenvalue-ratio identity** (this is the gap `RESULT_cap_reducibility_analysis_v1.md`
§4 already flags). Katz does not draw the bridge↔eigenvalue link explicitly.

## What the link would require (honest)

`[LENS-CONJECTURE]` A real proof would need to show: the $\mu_3$ acting on the
cubic-residue-symbol side (Matthews's CM elliptic function, the bridge arithmetic) and the
$\mu_3$ acting on the eigenvalue side (Frobenius on $H^1_c(L_{\chi_2(y)}\otimes L_{\chi_a})$)
are **the same automorphism of the same CM object.** The path:

1. Recognize $V(a)$ as a finite-field Mellin transform (Katz framework — done in the record).
2. Recognize the bridge's $\chi_3$ symbols as CM elliptic function values (Matthews 1979 —
   literature).
3. Show both $\mu_3$'s are the automorphism $(x,y)\mapsto(\omega x, y)$ of the underlying
   $j=0$ curve — the CM endomorphism — acting on the two sides of the same convolution.
4. Conclude: monodromy preserves $\alpha_2/\alpha_1 = \zeta_3$ uniformly because the
   preserving automorphism IS the CM endomorphism, which is present for every $a$ and every
   $p\equiv 1\bmod 3$.

**Step 3 is the load-bearing unproved step.** It is consistent with everything in the record
(the ω-descent, the within-cell exactness, the SU(2) absolute angle), and it would close
Frontier #26 if it holds. But it requires exhibiting the $\mu_3$ inside $G_{\text{geom}}$
acting internally on $H^1_c$ — which is exactly what R-B5.39 retracted for the *equivariant
sheaf* version, and what `PREREG_glv_lock_chirality_v1.md` retired for the *chirality*
version. **The category error those retractions flagged must be avoided**: a $\mu_3$ acting
on the family index $a\mapsto\lambda a$ (proved, ω-descent) is *not* the same as a $\mu_3$
acting internally on $H^1(F_a)$ (retracted). The link conjecture requires the *internal*
action, on $H^1_c$ — a genuinely different and harder object.

## Honest calibration

- **The link is not known.** I searched Katz, Matthews, Stickelberger/Kubota literature,
  CM/Sato–Tate surveys (Kedlaya, TAYOU), and the $j=0$-specific papers (Ono, Elkies, Ishii).
  None states the bridge↔eigenvalue-ratio $\mu_3$ coincidence as a theorem.
- **The lens prediction is novel.** The through-line (Matthews + Fermat-embedding + Katz) is
  structurally consistent with it but no one has connected the dots.
- **It may be false.** The retractions (R-B5.39, R-B5.40, retired chirality prereg) show
  that two prior attempts to find an internal $\mu_3$ action failed for category errors.
  This conjecture is a third attempt along a different path (via Matthews's CM elliptic
  function identification); it could fail the same way.
- **It is not tractable to prove here.** A real proof needs $G_{\text{geom}}$ identification
  (Frontier #28), which is research-grade and beyond what I can do in this session.

## What this note does

It records the lens prediction as a **named, literature-grounded conjecture** with a clear
path (steps 1–4 above) and a clear load-bearing gap (step 3). It does not prove the link.
If the project ever engages a CM-theory expert or identifies $G_{\text{geom}}$, this is the
conjecture to test: *is the bridge's $\mu_3$ the CM endomorphism acting on $H^1_c$?*

## Sources

- [Matthews 1979, Kummer sum](https://eudml.org/doc/142647) — cubic Gauss sum = CM elliptic function value
- [Wikipedia: Kummer sum](https://en.wikipedia.org/wiki/Kummer_sum) — $\mathbb{Z}[\omega]$ setting
- [MathOverflow 512660: CM curves in Fermat Jacobians](https://mathoverflow.net/questions/512660) — eigenvalue-ratio-is-root-of-unity embedding criterion
- [Katz AM-180, *Convolution and Equidistribution*](https://web.math.princeton.edu/~nmk/mellin324book.pdf) — the finite-field Mellin-transform / Sato–Tate framework
- [Kedlaya slides: Equidistribution of Frobenius Eigenvalues](https://kskedlaya.org/slides/st-colloquium-umd.pdf)
- [TAYOU: Equidistribution of Frobenius Eigenvalues](https://www.dpmms.cam.ac.uk/~jat58/Frobenius.pdf)
- [Ishii 2004: Trace of Frobenius, CM elliptic curves](https://ui.adsabs.harvard.edu/abs/2004math......1289I/abstract)
- [Ono: Distribution of Hypergeometric Values](https://uva.theopenscholar.com/files/ken-ono/files/gaussiandistributioncorrectedaftersubmission.pdf) — $j=0$ character-sum evaluations
- [Heath-Brown: Kummer's conjecture for cubic Gauss sums](https://ora.ox.ac.uk/objects/uuid:16c3966e-61cb-499d-839c-559b3794fcff)
- [Dunn–Robles: Patterson's conjecture (bias in cubic Gauss sums)](https://arxiv.org/html/2109.07463v3)
