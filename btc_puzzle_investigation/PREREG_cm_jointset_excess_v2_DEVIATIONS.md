# DEVIATIONS — PREREG_cm_jointset_excess_v2.md (A-joint)

Post-freeze notes, disclosed per the prereg's freeze protocol.

---

## Second-read gate: DISCHARGED (2026-08-21) — v2 RUNNABLE AS FROZEN

An independent `experiment-designer` second read audited v2 against the 9-item checklist, verifying every
mechanical claim in code (`model_curve_infra_v1.py`, `schedules_v1/schedule_A_joint_v1.json`). **All 9
items PASS; verdict: runnable as frozen, no item blocks it.** Confirmed in code:
- PC-SEM builds in ~3 resample draws, non-degenerate (`#distinct(Ψ_planted)=3`, `S₃≠0` on 100%), and
  fires monotone: `Î_prim` = 0.016 → 0.059 → 0.127 → 0.487 bits over `ρ∈{0,0.15,0.30,0.60}`, exact
  within-stratum perm p<0.01 for `ρ≥0.15`; `Φ^pt` does not absorb it (Ψ takes ≥2 values in all 27/27
  strata); the `ρ=0` baseline = plug-in bias floor with perm p=0.43 (correctly non-significant).
- `s=27` strata, `df=108`, `λ₈₀=54.87`, `MI_min = 7.92×10⁻³` @5k / `1.98×10⁻³` @20k — matches §5.
- Anomalous exclusion gates `N==q` (j0) and `t==1` (jgen); schedule reproduces bit-exact (SHA
  `c533f669…1406`); discovery/confirmation/ladder traces all ≠ 1; 547 correctly dropped.
- Signal path float-free (`check_no_float.sh` exits 0); Semaev S₃ 60/60 true relations vanish.

The Owed-gate "second independent experiment-designer read of THIS v2" is thereby **DISCHARGED**.
Remaining owed: `compile-diff` only if this line is later folded into a master/handover.

## Disclosure 1 (item 3, non-blocking) — the cited `I(Ψ;Φ^pt)` magnitude is plug-in-biased

§3 (v2) cites `I(Ψ;Φ^pt)=0.0083 bits` to justify "the within-stratum and global nulls provably differ."
The **exact-law** value (all 64³ triples, q=541) is `3.7×10⁻⁴ bits`; the `0.0083` is finite-N plug-in
MI bias (≈`(81−3−27+1)/(2·5000·ln2)`). **The load-bearing claim holds** (`I(Ψ;Φ^pt) > 0` ⇒ the two
nulls differ, so the within-stratum null is required). **Run-log action:** report the exact-law
`3.7×10⁻⁴` and treat `0.0083` as the plug-in estimate; do not cite the biased figure as the structural
magnitude. (Statistic/null/power unchanged.)

## Disclosure 2 (item 8, non-blocking) — the Δ paired-sign contrast has coarse resolution

The `Δ` paired CM/non-CM sign contrast over the **3 discovery primes** alone has minimum resolution
`p = 1/2³ = 0.125` — it cannot itself reach `p≤0.01`. The §7 `p≤0.01` significance correctly rests on
the **per-arm within-stratum permutation null** (well-powered per §5), NOT on the paired sign. **Run-log
action:** state this so "`Δ>0` at `p≤0.01` across discovery" is not misread as achievable by sign alone;
the paired sign is a direction/consistency check, the per-arm null carries the significance. (The full
schedule — discovery+confirmation+ladder = 10 primes — gives the paired sign min `p=1/2¹⁰`, adequate for
a directional confirmation across the whole schedule.)

**Both disclosures are run-log clarifications, not spec changes; v2 stands runnable as frozen.**
