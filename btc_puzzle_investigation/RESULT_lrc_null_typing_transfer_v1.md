# Retyping the lift×band null under the LRC coverage-transport taxonomy (v1, 2026-07-23)

**Object:** the two nulls recorded in `lift_band_joint_findings_v1.md` (Part 1 MI grid; Part 2 overlap
arm). **No new computation.** This document re-reads evidence already printed in that file against a
four-way taxonomy imported from the LRC coverage-transport programme
(`../lrc_global_mechanism_synthesis_v1.md` §3, `../lrc_discrepancy_findings_v1.md` §5).

**Decidable artifact:** a typing assignment per arm, each backed by a number the source file already
prints, plus two specific claims about arm power that are checkable from the source scripts.

---

## 1. The imported taxonomy

The LRC programme does not treat "coverage = 0" as one outcome. It splits into four structurally
distinct primitives, each with a different consequence:

| primitive | definition (LRC) | signature | what a null means |
|---|---|---|---|
| **Static dropout** | the sole coverer was removed; capacity was exactly 1, now 0 | the covering object is absent | real absence |
| **Transparency** | capacity is structurally ∅ — `bad(e,t,n)=∅` iff `t mod g ∈ {1,…,g−2}`, fraction `(g−2)/g` | the object is *active* but contributes zero | **uninformative** about coupling: nothing to transport |
| **Misalignment** | capacity ≠ 0 but aimed at the wrong residue class | structure present, measured in a coordinate that cannot see it | **relocate the readout**, do not conclude |
| **Handoff failure** | capacity exists on both sides, the Cond1/Cond2 transport gate blocks it | two live objects, no admissible transfer | the gate is the finding |

The point of the taxonomy is that only the first is "no structure." The LRC proof's safe fibres come
from the middle two, not the first.

---

## 2. Typing the arms

### 2.1 Curve-side readouts → **TRANSPARENCY** `[from Part 2's own numbers]`

Part 2 records, for `eis_u, eis_v, norm_s, flap_eps, sextant, sign_xy`:

> low-frequency excess **~1.0×** (0.7–1.3×, converging to 1.0 as L grows; the 1.4× wobble at n=2089
> washes out by n=33151).

Convergence *toward* the floor as `L` grows is the transparency signature, not a magnitude bound that
might tighten with more data. These readouts have no above-floor mass to contribute in `d`. A null
measured against them is a fact about the readout's capacity, and carries no information about whether
a coupling exists.

### 2.2 Band side → **MISALIGNMENT**, and the source file contains both halves `[object-level]`

Part 2 records the opposite for the denominator:

> `k_den = n(d)` (the Farey denominator) carries low-frequency mass growing with curve size:
> **excess 5.4× → 12.2× → 28.0×**, with a **stable top mode |f| = 12/24/24**.

Growing with curve size ⇒ capacity is present and increasing. Now compare Part 1's target list:

> Targets (stored decomposition, exact): `derr=|n·off−k·A|, k mod 8, n mod 8, D mod {8,16}, |D|`.

**`n mod 8` in Part 1 and `k_den = n(d)` in Part 2 are the same functional** — verified at source level,
not by the label. Part 1's stored `n` comes from `exact_core.best_nk(d, N, nmax=256)`:

```
lo = 1 << (N-1);  num = d - lo
k = (2*num*n + lo) // (2*lo);   a = abs(num*n - k*lo)      # minimise a over n
```

Part 2's `k_den` comes from `lift_band_spectral_v1.band_residual(off, A, M)`:

```
off = d - A;  A = 1 << (bexp-1)
k = (2*den*off + A) // (2*A);   e = abs(den*off - k*A)      # minimise e over den
```

These are the same expression under `num↔off`, `lo↔A`, `n↔den`, including the half-up rounding and the
exact integer error. Part 1's `derr` is that same `e`.

**Caveat, recorded:** the denominator caps differ (`nmax=256` vs `M ∈ {32,48,64}`) and the scales differ
(Part 1 = real 256-bit band; Part 2 = toy curves `n ≤ 33151`). Same construction, different truncation —
so the two level sets are not identical, and the cross-part comparison is between the same functional at
two caps, not between two runs of one experiment.

Part 1 reads this object through a mod-8 *value* reduction; Part 2 finds the structure in its
*positional* Fourier profile as a function of `d`. A mod-8 residue of `n(d)` is blind to low-frequency
positional mass in `n(d)` by construction — the two are different functionals of the same sequence.
Part 1's floor and Part 2's 28× excess are therefore not in tension; they are capacity present (Part 2)
read through a coordinate that cannot see it (Part 1). That is Primitive 4 exactly.

The same split appears *within* Part 2: `derr` also has capacity, but at the other end of the spectrum —
excess 0.1–0.2× at low frequency, mass pushed high, top mode **154 → 442 → 782 growing with L**, versus
`k_den`'s **stable** top mode. Two live objects in disjoint spectral regions.

### 2.3 The overlap arm → **conditionally void, not an independent null** `[checkable from the script]`

Part 2's third arm reports *"every |z| < 1.8"* for each curve readout crossed with `derr` and `k_den`.
Reading `lift_band_spectral_v1.py`, that statistic is a Pearson correlation between two mean-removed
low-frequency power vectors, ranked against a permutation of the curve-readout vector. Given §2.1 —
every curve readout's low-frequency spectrum is at the white floor — the curve-side input to that
correlation is noise, so the correlation is with noise and the arm **could not have fired**. Its
outcome was fixed by the transparency result upstream of it.

Two consequences, both checkable:

1. **The overlap arm has no planted positive.** `lift_band_spectral_v1.py` contains `shuffle_floor`
   (a null) and no plant. Per `btc_puzzle_pubkey_relations_controlled_2026_07_18` — *audit old nulls
   for a firing control before trusting them* — this arm is in the flagged category.
2. **Its null should not be counted as independent evidence.** The file's summary lists it alongside
   the Part-1 grid as a separate confirmation ("no interference / no shared mode"). It is downstream of
   §2.1, not parallel to it.

This does not make the arm wrong. It makes its null uninformative at the stated scope, for a nameable
reason, which is a sharper statement than "|z| < 1.8."

---

## 3. What changes

| before | after |
|---|---|
| one pooled null: "lift features do not couple to the band at ~2% leak strength" | a **split**: curve readouts transparent (no capacity); band side has large, growing capacity read through a blind coordinate |
| `k_den`'s 28× excess recorded as an aside labelled "★ POSITIVE" | `k_den` is the **live object**; Part 1's floor is a property of the `mod 8` readout, not of `k_den` |
| overlap arm = a third independent null | overlap arm = **conditionally void** (input at the floor, no plant) |
| next step unclear | next step named: measure `k_den` in a coordinate that can see positional structure (§4) |

No previously reported number is retracted. The Part-1 magnitude bound stands **as a bound on the
tested features against the tested targets** — the retyping changes what that bound licenses, not
whether it holds.

---

## 4. Named next object — the `|f|` = 12/24/24 mode `[HYPOTHESIS — SPECTRAL HALF SINCE REFUTED]`

> **UPDATE 2026-07-23, same day.** Both halves were pre-registered and run.
> **(H2, geometry) CONFIRMED and derivable** — `L_q` is exactly the `φ(q)`-interval primitive comb,
> 0 mismatches over 675 840 offsets / 8 out-of-sample configs (`RESULT_kden_ramanujan_comb_v1.md`).
> **(H3, spectrum) REFUTED** — the equal-width Ramanujan factorization was killed by its own
> pre-registered clause (`R2_ram < 0.30` and `ΔR2 ≤ 0` on 8/8; `R2_ram` is *negative* everywhere while
> the **incoherent** model is positive). The `φ(q)` intervals of a given `q` do **not** share a common
> width, so the phases add incoherently and no Ramanujan-sum coherence arises
> (`RESULT_kden_h3_spectral_v1.md`). **The mechanism proposed below for `|f| = 24` is therefore wrong.**
> `H3-top` scored 0/8, and the `12/24/24` reading is now itself a candidate artifact of the weak
> value-shuffle null. The paragraph below is kept as written for the record.

`k_den(off)` is the best-rational-approximation denominator of `off/A` capped at `M`. The level set
`{off : k_den(off) = q}` is a union of intervals centred on the fractions `j/q` — and there are exactly
**`φ(q)`** such fractions with `gcd(j,q)=1`. If that identification holds, the Fourier transform of
each level-set indicator is a **Ramanujan sum**

```
   c_q(f) = Σ_{gcd(j,q)=1} e(jf/q) = μ(q/gcd(q,f)) · φ(q)/φ(q/gcd(q,f)),
```

so `k_den`'s power spectrum is a weighted superposition `Σ_q w_q |c_q(f)|²`, maximised at frequencies
`f` divisible by many `q ≤ M`. Observed top modes 12 and 24 are the small highly-composite integers —
**consistent, but in-sample**: those three configurations have been seen, so they cannot confirm the
hypothesis.

Two decidable consequences, the first object-level and the second spectral:

- **(H2, primary)** the number of maximal constant runs of `k_den` at value `q` is **exactly `φ(q)`** —
  an integer count, no spectrum required;
- **(H1, secondary)** above-floor modes concentrate at highly composite `f`, tested **out of sample** on
  fresh `(bexp, M)` including `M` prime and `M` highly composite, so the prediction is not confounded
  with `M` itself.

Falsification, plants, matched nulls (including a null preserving run structure but randomising run
positions, so piecewise-constancy alone cannot be credited as structure), power, and the confirmatory
`(bexp, M)` set are being frozen in `PREREG_kden_ramanujan_comb_v1.md` before any of it is run.

If (H2) holds, the totient is governing the band decomposition directly — the same functional the φ(n)
law places at the centre of the AP isolation structure. That would be a characterization of the band,
**not** a leakage result: `k_den` is a function of `d` only, and a law describing it says nothing about
recovering `d`.

---

## 5. Grades

| item | grade |
|---|---|
| curve readouts at the white floor with `L`-convergence (excess ~1.0×) | `[VERIFIED]` — Part 2's printed numbers |
| `k_den` low-frequency capacity 5.4×→12.2×→28.0×, stable top mode | `[VERIFIED]` — Part 2's printed numbers |
| `n mod 8` (Part 1) and `k_den` (Part 2) are the same functional | `[VERIFIED at source]` — `exact_core.best_nk` vs `band_residual` are the same expression; caps differ (256 vs 32/48/64) |
| a mod-8 value reduction cannot see positional low-frequency mass | `[PROVED]` — different functionals of the same sequence |
| typing: curve side transparent / band side misaligned | `[ARGUED]` from the two rows above |
| overlap arm could not have fired given §2.1; has no plant | `[VERIFIED]` — read `lift_band_spectral_v1.py` |
| Ramanujan-comb law for `k_den` (H1, H2) | `[HYPOTHESIS]` — prereg in flight, nothing run |

**No ECDLP content.** Everything here concerns `k_den(d)` and the spectral profile of readouts in `d`;
no claim is made about recovering `d`, and the Part-1 magnitude bound is unchanged.

*Grade legend: PROVED · VERIFIED (exact/numeric at scale) · ARGUED · EMPIRICAL (scoped, controls fired) ·
HYPOTHESIS · CITED.*
