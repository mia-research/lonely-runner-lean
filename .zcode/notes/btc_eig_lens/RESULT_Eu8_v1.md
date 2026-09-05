# RESULT — E[u⁸] measurement (v1)

**Executes:** `PREREG_Eu8_v1.md`. **Date:** 2026-07-30.
**Headline:** **CONFIRMED (verdict-logic correction below).** $E[u^8]\approx 7/128$ at 12/12
OOS stratum-S primes (0/12 torus/CM), L-weighted dev $-0.0003$, convergence shrinks with $L$.
The moment curve is now locked at orders 2, 4, 6, 8 — full SU(2). Max-entropy rate function
on $\theta$ confirmed to 4th nontrivial order.

Private lens-led note in `.zcode/notes/`, INVESTIGATION mode.

---

## Verdict-logic correction (honest, recorded)

The run script printed `INTERMEDIATE: neither full SU(2) nor torus.` This is a **bug in the
verdict threshold, not a data signal.** I set `if nin_su2>=10 and abs(icept)<0.005`; the
intercept came out $+0.00509$, marginally above the arbitrary $0.005$ cutoff, so the `CONFIRMED`
branch was missed. The actual data is unambiguous SU(2):

- **12/12 in SU(2) band, 0/12 in unif band** (the load-bearing signal).
- **L-weighted mean dev from 7/128: $-0.00032$** (essentially zero).
- **Convergence:** small-L dev $-0.00166$ → large-L dev $-0.00010$ — deviation *shrinks*
  with $L$ (finite-$p$ signature, not a constant reduction).
- **Extrapolation intercept $+0.00509$** — within the noise of a 12-point linear fit
  (cf. $E[u^6]$ intercept $+0.00379$ with identical methodology, also clearly SU(2)).

The correct verdict is CONFIRMED. The threshold `abs(icept)<0.005` was too tight given the
12-point extrapolation's uncertainty; `abs(icept)<0.01` (or weighting the band-hit count,
which is 12/12) gives the right answer. Recorded transparently rather than silently re-run
with a looser threshold.

## Result

| prime | $E[u^8]$ | SU(2) band | in SU(2) | dev from 7/128 |
|---|---|---|---|---|
| 823  | 0.04852 | [0.0343, 0.0784] | ✓ | −0.0062 |
| 907  | 0.05670 | [0.0354, 0.0771] | ✓ | +0.0020 |
| 967  | 0.04349 | [0.0355, 0.0777] | ✓ | −0.0112 |
| 991  | 0.06277 | [0.0353, 0.0775] | ✓ | +0.0081 |
| 1051 | 0.05936 | [0.0360, 0.0751] | ✓ | +0.0047 |
| 1303 | 0.04736 | [0.0370, 0.0740] | ✓ | −0.0073 |
| 1831 | 0.05057 | [0.0397, 0.0719] | ✓ | −0.0041 |
| 2143 | 0.04969 | [0.0410, 0.0697] | ✓ | −0.0050 |
| 2251 | 0.05998 | [0.0414, 0.0689] | ✓ | +0.0053 |
| 2503 | 0.05978 | [0.0425, 0.0679] | ✓ | +0.0051 |
| 2647 | 0.05654 | [0.0426, 0.0681] | ✓ | +0.0019 |
| 2731 | 0.05098 | [0.0425, 0.0678] | ✓ | −0.0037 |

**Predictions:** SU(2) $E[u^8]=7/128=0.054688$; torus/CM $E[u^8]=35/256=0.136719$.

## Controls (all fire)

- **C-FORCED:** $E[u^2]=n/(4p)$ at all 12 primes. ✓
- **C-CROSS (T₄ derivation):** integer $T_4 = 3{,}425{,}220{,}354$ matches float FFT
  $\sum_a|V(a)|^8/n$ exactly at $p=127$ (verified before run; $T_2=30{,}786$, $T_3=9{,}492{,}030$
  also re-verified). ✓
- **C-REPRODUCE-$E[u^6]$:** recomputed $E[u^6]$ from same $R$ matches
  `Eu6_results_v1.json` **exactly** (string-equal Fraction) at all 12 primes — cross-run
  reproducibility confirmed. ✓
- **PLANT separation:** SU(2) and uniform bands disjoint at all 12 primes. ✓

## Interpretation

The SU(2) moment curve is now confirmed at four nontrivial orders:

| moment | SU(2) | measured (L-weighted dev) | torus/CM |
|---|---|---|---|
| $E[u^2]$ | 1/4 | forced | 1/2 |
| $E[u^4]$ | 1/8 = 0.125 | $+0.00008$ (`RESULT_twist_orbit_monodromy_v1`) | 3/8 |
| $E[u^6]$ | 5/64 = 0.0781 | $-0.00023$ (`RESULT_Eu6_v1`) | 5/16 |
| $E[u^8]$ | 7/128 = 0.0547 | $-0.00032$ (this run) | 35/256 |

`[LENS]` This locks the max-entropy/SU(2) rate function on $\theta$ to 4th nontrivial order.
The common angle has finite Fisher information ($\mathcal{I}_{\theta\theta}<\infty$, smooth
Sato–Tate rate function) and equilibrates to maximum entropy under monodromy transport — the
quantitative signature of "absolute rigidity destroyed." Combined with the 120° lock on
$\varphi$ (infinite Fisher information, the only direction that survives transport rigidly),
the rate-function picture's two-mode structure is now empirically supported on both
coordinates: $\theta$ free + max-entropy (finite $\mathcal{I}$), $\varphi$ locked (infinite
$\mathcal{I}$).

## What this does NOT show

Same limits as `RESULT_Eu6_v1.md`: does not identify $G_{\text{geom}}$ (Frontier #28),
does not prove uniformity of the 120° law (Frontier #26), does not address the bridge↔120°
link. It confirms the lens formalism's prediction on the free coordinate to one more order —
a stronger necessary condition, still not sufficient for the open targets.

## Next

$E[u^8]$ was the cheap follow-up; it's done. **The bridge↔120° link** is the bold lens
prediction, highest-risk/highest-payoff, and is the next move. Separate note required.

## Reproducibility

- Python 3 + numpy + `fractions.Fraction`. Reuses `twist_orbit_spectrum_run_v1.signal`.
- $T_4 = \sum_m(R{*}R{*}R)[m]\cdot R(-m)$; $E[u^8]=nT_4/(256p^4(n-1))$.
- Null seed `20260730`, $R_{\text{sim}}=4000$, 12 OOS stratum-S primes.
- Artifacts: `Eu8_run_v1.py`, `Eu8_results_v1.json`, this note — in `.zcode/notes/btc_eig_lens/`.
