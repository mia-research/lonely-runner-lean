# RESULT — T2d soft exclusion (public V → residue of d): SCOPED NULL; the χ3 hint was noise. Fence premise.

**Date:** 2026-08-16. **`[EMPIRICAL — SCOPED NULL; plant-fired]`.** Runs `PREREG_soft_exclusion_dmodk_v1.md`.
**Artifact:** `scratchpad/t2d_soft_exclusion_run_v1.py`. Signal path exact int; G/entropy are float
statistics ranked vs integer permutation nulls (verdict = Holm over the integer permutation p-values).

## Question
Does the public invariant vector `V=(χ3-index, eps, χ2(y))` statistically under-represent residues of
the SECRET scalar (`d mod k`, `k∈{2,3,4,6,7}`), removing bits from `d`'s range — beyond a matched
within-μ6-orbit control? This is the SOFT version after hard exclusion (empty cells) came back null,
and the properly-powered test of the lead I had earlier mislabeled dead (the public χ3-index varies for
all keys; I had conflated it with the trivially-zero scalar index).

## Result — no soft exclusion beyond control on the scan curves
One rep per ⟨±λ⟩-orbit (removes the forced coupling); B=3000 permutation control; Holm over the k-family.

| curve | U | k=2 | k=3 | k=4 | k=6 | k=7 | Holm survivors |
|---|---|---|---|---|---|---|---|
| p=547 | 91 | p=0.18 | 0.96 | 0.11 | 0.73 | 0.54 | NONE |
| p=907 | 161 | p=0.20 | 0.98 | 0.48 | 0.97 | 0.70 | NONE |

`bits_removed_net = H_ctrl − H_real ≈ ±0.05` (consistent with zero) for every k. Plants: positive
`pos_ok=True` (`G_pos`=200/354 ≫ control), negative `G_neg`≈0.6–1.5 (in-band). **No Holm survivor ⇒ no
OOS confirm needed.**

- **The raw χ3 hint (χ3=2 row 32/37/43, one curve) did NOT survive** the matched-control omnibus — it
  was finite-sample noise, as pre-flagged. Correctly not claimed.
- **Fence premise:** scoped null bound to {V=(χ3,eps,χ2y), k∈{2,3,4,6,7}, curves p=547/907, U≤161,
  V_detect≈0.2–0.3, plant fired}. NOT "impossible / no exclusion" — a sub-~0.2-bit soft exclusion is
  below this power and not excluded; confirm curves (U to 348, V_detect~0.13) were not needed (no scan
  hit) but would tighten it.

## Net for the T2 extraction/exclusion track (recorded straight)
Across the accessible curve sizes: no public-feature → d-carry (family), no hard exclusion (empty
cells), no soft exclusion (this) beyond matched controls, all plant-fired and powered to V≈0.2–0.3.
This is a coherent scoped null on the public-per-point-readout → d-residue avenue at reachable scale —
**scoped, not a wall.** The suppression I caught (mislabeling the public χ3 bit dead) is resolved: the
bit is real and public, and it does not (at this power) carry a residue of d.

## Still open (not touched by this)
- **Track 1** — the c=±b diagonal PHASE (T1a) and the −13.99σ deficit vs correct-shape null (T1b.1),
  via `PREREG_cbpm_phase_deficit_v2.md`. The deficit is the one real control-surviving anomaly; its
  phase/correct-null test is UN-RUN.
- **y-axis SIGN channel** — the free part of the forced-real y-sum `U(a,0,c)` (`RESULT_t1b_yaxis_forced_v1.md`).
- **Parallel fence-line** — any public invariant of `[d]G` computable from `d` in < 1 scalar-mult (GLV
  proves ≥1 exists). Open.
