# NOTE — N7 deficit localizes with an x/y asymmetry: super-Rayleigh on the x-axis, AMPLIFIED sub-Rayleigh on the y-axis (χ₂(y)-cover direction)

**Date 2026-08-18.** Two PRE-COMMITTED characterizations built on
`RESULT_subrayleigh_cubic_coherence_v1.md` (α). Neither is a new verdict-bearing test:
**Probe 1** executes the `X1` subspace-localization secondary of the FROZEN
`PREREG_subrayleigh_deficit_scaling_v1.md` ("report D restricted to strata {b=0},{c=0},{b=c},generic
complement … cannot change the primary verdict"), which had never been run; **Probe 2** executes the
`MC-HP` control defined in FROZEN `PREREG_subrayleigh_cubic_coherence_v1.md` §4. Script:
`scratchpad/cubic_coherence/probes12_v1.py` (exact-int signal path via `signal_path_v1`, `check_no_float`
clean; float transform carve-out). **Grade `[EMPIRICAL — characterization, 6–10 model primes]`.**
Model scale only (E: y²=x³+7, p ≤ 6571); **nothing transfers to secp**. N7 remains OPEN.

---

## Probe 1 — the N7 mean|U| deficit by stratum (D>0 sub-Rayleigh; D<0 super-Rayleigh)

Character vs matched Hermitian unit-phase null (the established N7 null), K=60 draws, full `U(b,c)`:

| p | c=0 (x-only) | b=0 (y-only) | b=c | bulk | GLOBAL |
|---|---|---|---|---|---|
| 349 | −1.957% | **+0.236%** | +0.689% | +0.145% | +0.141% |
| 577 | −1.395% | **+3.114%** | +0.265% | +0.084% | +0.086% |
| 823 | −0.874% | **+1.246%** | −0.587% | +0.138% | +0.137% |
| 1093 | −0.453% | **+1.924%** | −2.307% | +0.085% | +0.084% |
| 1471 | −0.040% | **+0.965%** | +2.894% | +0.109% | +0.112% |
| 1987 | −1.141% | **+2.371%** | +0.887% | +0.076% | +0.077% |

**Read:**
- **x-only (c=0): super-Rayleigh, 6/6 negative** — confirms α (Weil-bounded `|T|≤~4√p`, more uniform).
- **y-only (b=0): sub-Rayleigh AND AMPLIFIED, 6/6 positive** (+0.24% … +3.11%), roughly **10–40× the
  global per-frequency rate**. The deficit is *strongest* on the y-coordinate axis.
- **bulk (b≠0, c≠0, b≠c) ≈ GLOBAL** (+0.076% … +0.145%) — the deficit's **mass** is the generic bulk;
  the global rate is the bulk rate.
- **b=c diagonal:** sign-scattered (−2.3% … +2.9%), high variance on a `p`-frequency stratum — no call.

**The picture (honest, mass-aware).** By mass the deficit is a **bulk** phenomenon (the b=0 and c=0 axes
are each 1/p of the frequencies, so neither *sources* the global deficit — the F1 mass argument still
holds). But **per frequency** there is a clean **x/y asymmetry**: the x-coordinate direction *reverses*
the deficit (super-Rayleigh), while the **y-coordinate direction amplifies it** an order of magnitude.
The y-axis is `U(0,c)=Σ_d e_n(a₀d) e_p(c·y_d)` — the χ₂(y)-cover / y-coordinate channel, i.e. the same
object as `V(a)=Σ_P χ₂(y_P)e_n(a·d)` (Part A M4, N1) and the `A_new` spectral thread (Thread 1). **This
is where N7's per-frequency signal is strongest**, and it is exactly the object whose proved neighbors
(twist-orbit forced landscape, sub-Weil reduction, the ½-saturation N1) already live.

## Probe 2 — is the x-slice super-Rayleigh character-specific, or a generic unit-weight artifact?

c=0 slice L1: character vs permuted-character (MC-HP: destroys the d↦[d]G progression, keeps the exact
value multiset + Hermitian symmetry) vs random-magnitude null B0. K=40 MC-HP draws.

| p | Dchar/B0 | DMCHP/B0 |
|---|---|---|
| 349 | −1.682% | −0.100% |
| 577 | −0.946% | −0.000% |
| 823 | −1.159% | +0.060% |
| 1093 | −0.483% | −0.164% |
| 1471 | −0.292% | −0.091% |
| 1987 | −1.111% | +0.015% |
| 2671 | −1.250% | +0.068% |
| 3607 | −1.240% | −0.015% |
| 4861 | −0.548% | −0.089% |
| 6571 | −0.867% | +0.050% |

**Read: the x-slice super-Rayleigh is CHARACTER-SPECIFIC.** `Dchar/B0` is **10/10 negative** (−0.29 …
−1.68%); `DMCHP/B0 ≈ 0` (scattered ±0.16%). Permuting the character to a generic unit weight (which
destroys the Weil-boundedness of the genuine sum, and with it the cubic coherence P18 — the two are
entangled and die together under MC-HP) returns a ~Rayleigh slice. So the super-Rayleigh is a real
structural property of the genuine character sum `Σ e_n(a₀d)e_p(b·x_d)` — not a null artifact and not
generic to any Hermitian unit weight.

---

## What this buys (build-on, not closure)

- **α reinforced:** the c=0 super-Rayleigh is real, character-specific structure (Probe 2), so the α
  refutation of "cubic coherence sources N7" rests on real structure being the *wrong sign* on that slice.
- **N7 sharpened onto the y-coordinate / cover:** the per-frequency deficit **amplifies on the b=0
  (y-only) axis** — the χ₂(y)-cover channel, Thread 1's `V(a)`/`A_new`. This is the concrete
  re-localization α promised, and it lands N7 next to its proved neighbors.
- **The x/y asymmetry is itself a new characterized object:** same curve, same character, opposite tail
  behavior on the two coordinate axes (x super-Rayleigh / y amplified-sub-Rayleigh).

## Owed / next probes (each its own prereg)
1. **Powered confirmation of the b=0 amplification** — a 30-prime, matched-null, one-directional test of
   the y-only slice deficit (as N7 itself got). 6/6 positive over 6 primes is a strong lead with high
   magnitude scatter; it wants N7's own statistical treatment before "amplified on y" is more than a lead.
2. **Connect to `V(a)`** — is the b=0 amplified deficit the same object as the ½-saturation (N1) /
   sub-Rayleigh on `V(a)`? Both live on the y-cover; test whether the b=0 slice deficit and the N7
   deficit-on-V(a) coincide.
3. The b=c diagonal is sign-unstable — a candidate for a targeted look, low priority.

## Scope
E: y²=x³+7 only; p ≤ 6571 (Probe 1 to 1987, full-U cost); K=60/40 null draws; a₀=1; matched Hermitian /
MC-HP / max-entropy nulls. Model scale — no transfer to secp. Characterizations of an established
(N7) object; they do not change any primary verdict, do not close N7, and name their owed powered tests.
