# LENS NOTE — Does the φ(n) law re-enter via the cubic character? (NEGATIVE, v1)

**Mode:** INVESTIGATION (lens-open). **Date:** 2026-07-30.
**Question (from Trent):** "Looks like a bit of an AP — is this where the φ(n) law re-enters?"
I.e., is the cubic character $\chi_3$ (order-3 $\phi(n)$-residue representation) the forcing
mechanism for the 120° eigenvalue law?

**Verdict: NO.** The apparent connection dissolves under analysis. The exact identities I
found ($V(\lambda a)=V(a)$; class-sums = 0) are forced by elementary orbit-counting plus the
$\chi_2$-balance of $y$-coordinates, not by a nontrivial multiplicative↔additive coupling.
The 120° law and the bridge $\mu_3$ remain genuinely separate objects.

This note records the negative so it isn't re-derived.

---

## The chain of probes (and where each died)

### Probe 1 — stratify $|V(a)|^2$ by cubic residue class of $a$
Found: at some primes (547, 1051) the mean is bit-identical across the 3 classes; at others
(127, 211, 823) it differs by 13–101%. **Inconclusive on its own** — the equality looked
like a symmetry, the inequality looked like a connection.

### Probe 2 — is $V$ an eigenfunction of multiplication by $\lambda$?
Found: $V(\lambda a)/V(a)$ has concentration $R=1.0000$, $|$ratio$|=1.000\pm0.000$, phase
$0°$, at all 8 primes. **Seemed like a real φ(n)-level symmetry.**

### Probe 3 — is $c_{\lambda d}=c_d$? (the triviality check)
Found: **yes, exactly** ($c_{\lambda d}=c_d$ at 100% of $d$, all 8 primes). So Probe 2's
identity is a **reindexing triviality**: $V(\lambda a) = \sum_d c_d\zeta_n^{\lambda a d} =
\sum_d c_{\lambda^{-1}d}\zeta_n^{ad} = \sum_d c_d\zeta_n^{ad} = V(a)$. **Probe 2 died here.**

### Probe 4 — but the class-sums being 0 was still striking. Forced or empirical?
Found: **forced.** Two cases:
- **Transversal** ($\chi_3(\lambda)\ne 1$): the orbit $\{d,\lambda d,\lambda^2 d\}$ crosses
  all 3 classes; $c_d$ constant on orbits ⟹ all 3 class-sums automatically equal ⟹ each =
  (total)/3 = 0 (total is forced: $V(0)=\sum_d c_d=0$ because $\chi_2(y)$ is balanced over
  $E(\mathbb{F}_p)$, a property of the curve not of $\chi_3$).
- **Non-transversal** ($\chi_3(\lambda)=1$): orbits stay in one class; class-sum = 0 then
  needs separate balance, which also holds — but again from $\chi_2$-balance of $y$, not
  from $\chi_3$.

**Neither case gives a nontrivial multiplicative↔additive coupling at the magnitude level.**
**Probe 4 died here.**

## What this rules out

`[LENS-NEGATIVE]` The cubic character $\chi_3(a)$ (the order-3 $\phi(n)$-residue
representation, acting on the *multiplicative* unit group) does **not** force or couple to
the magnitude $|V(a)|$ of the additive sheaf. The 120° law ($\alpha_2/\alpha_1=\zeta_3$) is
therefore **not** a consequence of the $\phi(n)$-residue structure at the magnitude level.

## What it does NOT rule out

- A coupling at the **phase** level (the bridge's $\chi_3$ might relate to the *argument*
  of $V(a)$, not its magnitude). Probe 2 saw phase $0°$ for $V(\lambda a)/V(a)$, but that's
  the trivial $c_{\lambda d}=c_d$ again; a nontrivial phase coupling would need a different
  probe (e.g. comparing $\arg V(a)$ to $\chi_3(a)$ directly, controlling for the trivial
  reindexing).
- The connection via **CM monodromy** rather than via $\phi(n)$-residue arithmetic. The
  `LENS_bridge_eigval_link_v1.md` conjecture (bridge $\mu_3$ = eigenvalue $\mu_3$ as the same
  $G_{\text{geom}}$ element) is *not* refuted by this — it lives at the monodromy level,
  which these probes don't touch. But it's also not *supported* by the $\phi(n)$-arithmetic
  level, which is what Trent's question was reaching for.

## The honest synthesis

`[LENS]` My earlier framing ("unitarity of the $\phi(n)$-residue representation forces the
eigenvalue ratio") was **too loose and is retracted.** Unitarity forces $|\alpha_2/\alpha_1|=1$
(purity), and Kronecker forces "a root of unity" — but the *specific* $\zeta_3$ is CM, not
$\phi(n)$. The RH programme's "unitarity $\beta$-forcing" and the secp 120° law have the
same *form* (unitary rep forces spectral value) but **different mechanisms**: RH's is
genuinely $\phi(n)$-residue unitarity; secp's is CM monodromy. They share a field
($\mathbb{Z}[\omega]$) but not a forcing law. The parallel is suggestive for the lens but
not a theorem, and the $\phi(n)$-arithmetic level does not deliver the connection.

## Files

- `analytic_phi3_stratify.py` (Probe 1)
- `analytic_phi3_exact_check.py` (Probe 2)
- inline probes (Probes 3, 4) in this session's bash
- This note

## Calibration

- All findings are exact (integer/rational arithmetic, no float in the structural checks).
- The negative is as informative as a positive would have been: it rules out the cheapest
  version of the $\phi(n)$-re-entry and clarifies that the bridge↔120° link (if real) lives
  at the monodromy level, not the residue-arithmetic level.
- I retract the "φ(n) law re-enters" framing from the prior message. Trent's instinct to
  think analytically caught an overstatement; the analysis corrects it.
