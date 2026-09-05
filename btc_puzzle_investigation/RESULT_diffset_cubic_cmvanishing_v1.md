> ## ⊘ HEADLINE SUPERSEDED (banner added 2026-08-04, retrospective audit)
> The headline below — *"curve fingerprint, not a d-fingerprint"* — and the "Rules out" clause were
> **WITHDRAWN** by `CORRECTION_e3_cmvanishing_interaction_reading_v1.md` (2026-07-31): a two-arm design
> sharing keys+null cannot license a curve-only reading; the effect is a **key-set × curve INTERACTION**.
> That correction's OWN status block then withdrew the *pursuit* as out of scope — E3's null is the
> known-MT19937 pool, so the test is a **generator test whatever the curve** ("check the null's
> provenance"). **The measurements below stand; the inference in the Interpretation / Rules-out sections
> does not.** Read those two sections as superseded. (Retrospective note: this stale headline nearly
> re-suppressed the finding on re-read — the fragmentation hazard the audit is about.)

# RESULT — CM-vanishing test for the E3 anomaly (v1)

**Executes:** `PREREG_diffset_cubic_cmvanishing_v1.md` (gate-signed-off, frozen before apply).
**Date:** 2026-07-28.
**Headline:** **FAIL-TO-REJECT on $E'$.** The freed-lens **CM-driven prediction is
confirmed**: the E3 anomaly ($E_3=13125$ on secp, $p\approx 0.033$) **does not survive** the
curve swap to a non-CM curve over the same prime. The secp anomaly is a **$j=0$ curve
fingerprint**, not a $d$-fingerprint.

Per the standing banners: this is a **characterization**, not a verdict. No security
implication is drawn. `secure` / `closure` / `proven hard` / `unbreakable` are not used.

---

## Setup

- **Same 82 real puzzle private keys $d$** (from `solved_puzzles_xy.csv`), mapped onto a
  **non-CM curve** $E': y^2 = x^3 + x + 1$ over **secp's prime** $P$. $j(E') \ne 0,1728$ ⟹
  no CM, no extra automorphisms.
- Generator $G'$ of prime order $n' \approx 2^{180}$ ($>2^{130}$, so all 82 $d\in[1,2^{130})$
  give distinct points; cofactor $h'\approx 2^{75}$ is large but does not affect the
  comparison — both cells use $[d]G'$ in the same subgroup). See `PREREG §Amendment Note`
  for the principled relaxation of the original $h'\le 4$ requirement.
- **$\chi_3$ is the field character over secp's $\mathbb{F}_P$ in BOTH cells.** Only the
  curve (hence the map $d\mapsto X$) changes. This isolates the curve variable cleanly.
- Matched null: the same 100,023 $d$-values from `constructed_keys_1to160_100k.csv`
  (known-MT19937, same bit-lengths), mapped onto $E'$. 10,000 resamples of 82.
- **Frozen region** (before any $E'$ real data was touched): $[L', U'] = [84, 12324]$,
  $\alpha = 0.0486$. Compare secp's frozen region $[84, 11997]$.

## Decision

```
class counts (a,b,c) = (1111, 1140, 1070)   sum=3321 ✓   E3 mod 3 = 0 ✓
E3'(real) = 3711
frozen region [L', U'] = [84, 12324]
decision:  FAIL-TO-REJECT
  E3' at ~67.1st percentile of E' null   (two-sided rank p ≈ 0.660)
```

| cell | real 82 $E_3$ | null mean | pctile | $p$ | decision |
|---|---|---|---|---|---|
| **secp** ($j=0$, CM) | **13125** | 3274 | **98.4th** | **0.033** | REJECT-HIGH |
| **$E'$** ($j\ne0$, non-CM) | **3711** | 3349 | **67.1st** | **0.660** | FAIL-TO-REJECT |

## Controls (all FIRE)

- **C1 forced-structure:** `a+b+c=3321`, `E3 ≡ 0 mod 3` on $E'$. ✓
- **C2 planted-firing** ($\varepsilon=0.05$ concentration plant on $E'$): power **0.938**
  ($\ge 0.9$ target). The instrument discriminates a planted signal on $E'$, so a null
  result is not an instrument failure.
- **C3 cross-check regen** (seed 4242, 2000 draws on $E'$): mean 3488, 2.5/50/97.5%
  $= 84 / 2439 / 13125$ — consistent with the frozen null ($84/2352/12324$) within sampling
  noise. ✓

## Interpretation

**The E3 anomaly is CM-driven.** The same 82 puzzle $d$'s that produce a 98.4th-percentile
cubic-residue concentration of pairwise $X$-differences on secp produce a 67.1st-percentile
value — i.e. a typical null draw — on a non-CM curve over the same prime. The anomaly does
not survive the curve swap, so it cannot be a property of the $d$'s themselves; it is a
property of the **interaction between the $d$-set's band structure and secp's $j=0$
endomorphism** $\phi:(x,y)\mapsto(\omega x, y)$.

In the freed-lens register (INVESTIGATION mode, tagged as conjectural): the cubic-residue
"magnetization" of the real key set is produced by the CM endomorphism acting on the
$X$-coordinate image. Removing the endomorphism (moving to $j\ne 0$) removes the
magnetization. The secp anomaly is a **curve fingerprint**, not a **key fingerprint**.

## What this rules out / does not rule out

**Rules out:** a $d$-structural reading of the E3 anomaly. The 82 puzzle $d$'s do not
themselves carry cubic-residue structure that would make $E_3$ anomalous independent of the
curve. The PRNG-fingerprint / puzzle-generator hypothesis (the "REJECT-HIGH on $E'$" branch)
is **not supported**.

**Does not rule out:** (i) curve-structural cubic bias on secp specifically — that is what
the test confirms, and it is what the secp E3 result measures. (ii) Group-law joint
difference-set objects (Frontier #29) on secp — these probe a different subspace ($P_i\pm P_j$
via curve addition, the CM-native operation) and may still carry structure that $E_3$ on
raw $X$-differences does not. (iii) The subpolynomial-extraction question — this test does
not address it; it addresses only whether E3's anomaly is $d$-driven.

## What this does NOT establish (honest)

- It is **not** a closure of the cubic channel on secp. E3 is a marginal-count statistic;
  it is blind to orientation-odd, joint/triangle, and band-localized subspaces (inherited
  caveat, `PREREG §Subspace caveat`). The fail-to-reject on $E'$ bounds only the pooled
  orientation-symmetric magnitude channel **on $E'$**.
- It is **not** a security verdict. A curve fingerprint being present does not imply
  extractability; the alignment-strength fence (`masked_structure_findings_v14.md`,
  computational not information-theoretic) is untouched by this result.
- It is **one** test in a family; the {secp E3, $E'$ E3} pair is 2 tests, and the $E'$
  result at $p\approx 0.66$ is unambiguous, but the secp-side $p\approx 0.033$ remains
  Bonferroni-non-significant at the family level.

## Next (lens-directed)

1. **The structure lives on secp.** Since the anomaly is CM-driven, the freed-lens avenue on
   this surface is curve-structural, not key-structural. The next lever is the **band-width
   phase scan on secp**: fix secp, sweep band width $w$ from consecutive ($w=1$) to uniform
   ($w=2^N$), measure $E_3(w)$. The lens predicts a phase transition at a critical band
   width $w_c$; if one exists, $w_c$ is the scale below which the CM cubic structure locks
   $d$.
2. **Group-law E3 on secp** (Frontier #29): $\chi_3(x(P_i-P_j))$ via curve addition, the CM
   endomorphism's native operation. Prediction: fires harder than the $X$-difference version
   because the group law is where CM acts.
3. **Rekeying-invariance of the 0.93 alignment** (the other freed-lens testable): if the
   joint-shadow alignment is rekey-invariant, it is curve structure masquerading as leakage
   (consistent with this result).

## Artifacts

- `PREREG_diffset_cubic_cmvanishing_v1.md` (frozen spec + Amendment Note)
- `cmvanishing_curve_setup.sage`, `diffset_cubic_Eprime_meta_v1.json` (curve params)
- `diffset_cubic_Eprime_derive.py`, `solved_puzzles_xy_Eprime.csv`, `constructed_keys_Eprime_100k.csv`
- `diffset_cubic_Eprime_null.py`, `diffset_cubic_Eprime_frozen_null_v1.npy`, `diffset_cubic_Eprime_frozen_meta_v1.json`
- `diffset_cubic_Eprime_apply.py` (controls + decision)

## Reproducibility

- Python 3.14 + gmpy2 2.3.1 + numpy; SageMath 10.9 for SEA point-counting (Step 1 only).
- Curve $E': y^2 = x^3 + x + 1$ over secp $P$; $n' = 1735267482095677159220328300040520133145015240816313753$ (181 bits).
- Null seed 20260728, $N=10000$; regen seed 4242, $N=2000$; planted seed 12345, $N=500$.
- Prereg SHA-256 at freeze: see `diffset_cubic_Eprime_frozen_meta_v1.json` `prereg_sha256_at_freeze`.
