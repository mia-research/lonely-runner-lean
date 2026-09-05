# NOTE — the A_new(F_p) subgroup-structure map: corrected picture, the automatic-√p identity, and the S-visibility question (in progress)

**Date 2026-08-22.** Trigger: the p=211 rung discovery. Status: the structural correction is
established; the S-visibility law is pinned to a character-class question with the sweep
(`anew_sorder_sweep_v1.sage`) grinding the ground truth.

## 1. Corrected picture: the GROUP is cyclic at squarefree M; the S-IMAGE may be proper

The 211 crash was read as "A_new non-cyclic." The algebra says finer: with char-poly
$f = T^4+pT^2+p^2$ (the verified baseline), for each prime $\ell^e \| M = p^2{+}p{+}1$ ($\ell \ne 3$;
every such $\ell \equiv 1 \bmod 3$ automatically since $p$ has order 3 mod $\ell$), root-1 of $f \bmod
\ell$ has multiplicity exactly 1 when $\ell \| M$ (two quadratics vanishing at 1 would force $\ell^2
| M$) ⇒ every Sylow is $\mathbb{Z}/\ell$ ⇒ **$A_{new}(F_p)$ is CYCLIC whenever $M$ is squarefree**
(the $\ell^2 \| M$ cases — 67, 79 with $7^2$ — need the Smith refinement). At 211, $M = 3 \cdot 13
\cdot 31 \cdot 37$ is squarefree ⇒ the group is cyclic and **what failed is the $S$-image**: the
isotypic readout lands in the index-13 subgroup. Two different objects — important for the transfer
question: the $k=3$ DLP instance itself is unaffected; the $c^+$ readout is partially blind.

## 2. The automatic-√p identity and the always-root-1 factor

Over $\mathbb{Q}(\sqrt p)$: $f = (T^2 - \sqrt p\,T + p)(T^2 + \sqrt p\,T + p)$ (verified:
product $= T^4+pT^2+p^2$; the pairing $\{\zeta_6^2,\zeta_6^4\}$/$\{\zeta_6,\zeta_6^5\}$ IS the
$\zeta_3$-eigenpairing — sum $\zeta_6^2{+}\zeta_6^4 = -1$, product $p\zeta_6^6 = p$). For
$\ell | M$: $r := 1{+}p \bmod \ell$ satisfies $r^2 \equiv p$ **automatically** ($r^2 - p = M$), so
$\ell$ always splits in $\mathbb{Q}(\sqrt p)$ with explicit witness $r$, and the root-1 factor is
always $T^2 - rT + p$ (check: $1 - r + p = 0$). So the 2-dim $\zeta_3$-eigenplane owning the
$\ell$-torsion is the one containing root-1 iff its canonical $\sqrt p$-sign matches $+r$ —
**S-visibility of $\ell$ is an embedding-sign question in $\mathbb{Q}(\sqrt p, \zeta_3)$**.

## 3. Ground truth so far (rungs + sweep)

| p | M | group | S-orders seen | S sees |
|---|---|---|---|---|
| 43 | 3·631 | cyclic ✓ | {631, 1893} | ALL |
| 67 | 3·7²·31 | (Smith owed) | {651, 1519, **4557**} | ALL incl. the 49-part |
| 163 | 3·7·19·67 | cyclic ✓ | {…, **26733**} | ALL |
| 211 | 3·13·31·37 | cyclic (squarefree) | {37, 111, 1147, 3441} | 31, 37; **blind to 13** |

## 4. The visibility law: not the plain Legendre

Candidate $s(\ell) = (\ell/p)$ fails (ℓ=37 at p=211: symbol $+1$ but SEEN). Empirical pattern so far:
**every $\ell \equiv 7 \bmod 12$ is seen (6/6)**; the $\ell \equiv 1 \bmod 12$ class is mixed
(13 blind, 37 seen) — the sign is a finer character (conjecturally the $\mathbb{Q}(\sqrt p,\zeta_3)$
embedding sign, a quartic-type character). The sweep (12 primes, `anew_sorder_sweep.json`) is
collecting the ground truth to fit it; the $\ell^2$ cases (67, 79) will also show whether S sees the
full $\ell^2$ or just $\ell$ (the Smith structure of the non-squarefree M).

## Consequences (interim)

- The ladder's clean rungs (S fully visible): 43, 67, 79?, 163, 823?, 1051? — the c⁺ statistic is
  well-posed exactly there; blind-part rungs (211: 13; 547?: 613) read $c^+$ mod the visible part —
  a documented deviation, not a failure.
- The transfer-bound reading: the subgroup hurdle is REAL but sits on the readout side ($S$-image),
  not the group side — the supersingular $k{=}3$ instance itself is untouched by it.

## §Update (2026-08-27, post-reset harvest): the sweep ground truth through p=1051

| p | M | S-order max | verdict |
|---|---|---|---|
| 43 | 3·631 | 1893 = M | FULL |
| 67 | 3·7²·31 | 4557 = M | FULL (incl. 49) |
| 79 | 3·7²·43 | 6321 = M | FULL (incl. 49) |
| 163 | 3·7·19·67 | 26733 = M | FULL |
| 211 | 3·13·31·37 | 3441 = M/13 | **13-BLIND (the only blindness observed)** |
| 547 | 3·163·613 | 299757 = M | FULL (613 SEEN — kills the naive Legendre law's prediction) |
| 823 | 3·7·43·751 | 678153 = M | FULL |
| 1051 | 3·368551 | 1105653 = M | FULL |

**S-blindness is RARE: 1 of ~25 (p, ℓ) points.** The isotypic readout is generically fully visible;
211's 13 is an isolated case so far (sweep continues toward 1303 — whose M again contains a 13:
if 1303 is also 13-blind, the character is ℓ=13-specific in a way that interacts with p; if not,
(211,13) is a sporadic embedding-sign event). The character-fit ambition narrows to: explain the
SINGLE blind point + the all-seen pattern — plausibly a rare sign coincidence in Q(√p, ζ₃) rather
than a clean global law.
