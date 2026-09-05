# RESULT — the Semaev-triple (collinear) sign probe: conditional coupling closed BY STRUCTURE; the third-order correlation is EXACTLY ZERO (a theorem at p≡3 mod 4); Vieta identities machine-verified

**Date 2026-08-22. Grade: `[VERIFIED — exact, total enumeration]`** for all small-p numbers;
`[PROVED — 4-line involution argument]` for the E[π] = 0 theorem. Script:
`m40_collinear_sign_probe_v1.py` (+ `.log`). Answers the Semaev-triple sharpening of the
N15∩M40 question (`RESULT_m40_triple_probe_v1.md` sequel; see also `RESULT_m40_n15_exact_accounting_v1.md`).

## The three closures

**1. The conditional question is the pairwise question.** For a collinear triple
$P_1 + P_2 + P_3 = O$: $f_3 = \chi_2(y_{P_3}) = \chi_2(-y_{12}) = \chi_2(-1) f(d_1{+}d_2)$ by the
proved antisymmetry. So "$MI(f_3; (f_1,f_2))$ on collinear triples" **is** the (g) pairwise statistic
$MI(f(d_1{+}d_2); (f_1,f_2))$ up to a relabeling — already measured flat off the forced anti-diagonal.
The Semaev sign-sieve constrains nothing beyond what the pairwise probe closed.

**2. The third-order correlation vanishes EXACTLY — a theorem.** $\pi = f_1f_2f_3$ on collinear triples
satisfies (Vieta, machine-verified on **all 83,744** enumerated secant/tangent pairs at 6 primes):
$y_1y_2y_3 = b^3 - 7m^3$, $x_1{+}x_2{+}x_3 = m^2$ (line $y = mx{+}b$), so
$\pi = \chi_2(m)\cdot\chi_2(t^3{-}7)$, $t = b/m$. The involution $(P_1,P_2) \mapsto (-P_1,-P_2)$ sends
$m \mapsto -m$, $b \mapsto -b$, $t \mapsto t$, hence $\pi \mapsto \chi_2(-1)\,\pi$.
**At every $p \equiv 3 \bmod 4$ the multiset of $\pi$ is antisymmetric ⇒ $E[\pi] = 0$ exactly.**
Verified exact (0.000000) at 43, 79, 127, 163, 211; secp sample $-0.0016 \pm 0.0032$ (N=100k,
consistent with 0). No average third-order signal exists in collinear sign products — on any
$p \equiv 3 \bmod 4$ curve, secp included.

**3. $E[\chi_2(m)] = 0$ exactly at $p \equiv 3 \bmod 4$** — same involution ($m \mapsto -m$ ⇒ antisymmetric
multiset). Verified exact at the five ≡3 mod 4 primes.

## The flagged residue (named, not closed)

$E[\chi_2(t^3 - 7)]$ over secant lines is persistently nonzero: +0.354, +0.214, +0.013, +0.181, +0.081
(p = 43, 79, 127, 163, 211), −0.014 (p=61, the ≡1 mod 4 arm). Mechanism open — plausibly the cubic
residuosity class of 7 mod p (all tested primes are ≡ 1 mod 3); the erratic p-pattern supports an
arithmetic driver. **d-relevance: none found and none structurally available** — $t$ is
involution-invariant, so this bias lives in the line family and is invisible to every
antisymmetrized ($\pi$-type) readout; it is a marginal of the line parameters, not of points.
A focused follow-up (exact, small cost): the p-dependence vs the cubic character of 7, i.e. whether
$E[\chi_2(t^3{-}7)]$ is nonzero iff 7 is (non-)cubic mod p. This is the complete residue of the
collinear-sign question.

## Consequence for the board

The N15∩M40 question is now closed at the sign level through order 3: pairwise flat (g), triple flat
(cube probe), collinear-conditional ≡ pairwise, third-order correlation identically zero (theorem).
**Any cheap alignment filter must live in non-sign readouts** (sextant/tuple-valued across points,
weighted multiset objects — E3-class, powered-bounded by N30 — or the Fourier $V(a)$ side), exactly as
(g)/(h) concluded — now with the sign world fully exhausted rather than partially sampled.

## §Resolution of the flagged residue (2026-08-22, same day — one script, `collinear_residue_pdependence_v1.py`)

Full enumeration at 13 prime-order primes $p \in [43, 577]$:

- **7 is non-cubic at EVERY prime-order prime — structurally.** If 7 were a cube, $x^3{+}7$ would have a
  rational root ⇒ rational 2-torsion ⇒ even order ⇒ excluded by the prime-order filter. The
  cube-residuosity driver hypothesis is therefore unfalsifiable on this family (and unneeded).
- **The driver is the twist trace:** $E[\chi_2(t^3{-}7)]_{\rm line} \approx -\langle\chi_2(t^3{-}7)\rangle_{\rm uniform}
  = t'/p$ at the same magnitude (ratio ≈ 1.1–1.5×), opposite sign, at essentially every prime — with
  $|E|\sqrt p \in [1.3, 3]$ not growing. **The bias is the twist-trace incomplete character sum at
  Weil scale $p^{-1/2}$; it vanishes at secp.** The earlier "persistent, non-decaying" read (6 primes
  ≤ 211) was the small-p window of a $\sqrt p$-fluctuating quantity. The t-multiset is uniform
  (dev ≤ 0.007, shrinking ~1/p).

**Collinear probe: fully closed.** Conditional coupling ≡ pairwise (flat); third-order correlation
identically zero (theorem); line-family residue = Weil-scale twist-trace effect, zero at secp.
