# RESULT — the buried-lead sweep, and the two items it named, both now closed

**Date:** 2026-08-01. **Scripts:** `joint_shadow_xonly_multiseed_v1.py`,
`mu3_forced_subspace_object_v1.py`. Companion: `RESULT_26_involution_mechanism_refuted_v1.md`.
**Trigger:** user challenge — *"I wonder how many more leads you have buried."* Answered by counting,
not by assurance.

---

## 1. Item 1 — the unbanked 4/4 sub-observation: CLOSED as seed noise

`RESULT_joint_shadow_decompose_v2.md` flagged, explicitly *"not banked"*: x-only phase-recon fidelity
for the **character** ran below the **random** target at all four primes (0.6699<0.6881,
0.6734<0.6749, 0.6633<0.6723, 0.6588<0.6609), and stated its own requirement —
*"needs a multi-seed null to place char in the random distribution."* **No follow-up existed.**

Defect: `joint_shadow_decompose_v1.py:184` draws **one** random target, `default_rng(p+1)`. 4/4
direction-consistency against one draw each is `1/16` under a fair coin — not evidence either way.

Re-run against **200 independent random targets per prime**:

| `p` | `n` | char | random min / med / max | rank |
|---|---|---|---|---|
| 163 | 139 | 0.6699 | 0.5815 / 0.6659 / 0.7730 | **115/200** |
| 349 | 313 | 0.6734 | 0.6018 / 0.6654 / 0.7168 | **127/200** |
| 433 | 397 | 0.6633 | 0.6198 / 0.6645 / 0.7038 | **93/200** |
| 577 | 613 | 0.6588 | 0.6146 / 0.6582 / 0.6926 | **103/200** |

Char values reproduce the recorded ones **exactly** — the instrument is validated. Ranks are dead
centre at every prime. **The 4/4 was seed noise. Sub-observation CLOSED.**
Scope: x-only phase-recon fidelity, these 4 primes, 200 seeds each. Readout is an integer rank; no
float threshold decides anything.

## 2. Item 2 — the `μ₃`-forced subspace: object BUILT, residual probed once

The thing I dismissed this morning, now constructed. Both forced symmetries **verified, not assumed**,
at 8 primes (`p = 43…823`): `h₁[m·d] = h₁[d]` (`m` order 3) and `h₁[−d] = ε·h₁[d]`, hence on
`(ℤ/n)*` written multiplicatively the sign sequence has period `(n−1)/3` and a further half-period
sign flip — **free content exactly `(n−1)/6`, matching `mu6_reps`' cell count.**

**POSITIVE, and it stands:** an exact, forced, `j=0`-specific constraint reducing `n−1` signs to
`(n−1)/6`. Present on secp256k1.

**Residual probe (one statistic):** max Fourier coefficient of the reduced sequence over the cyclic
quotient `Q₆`, ranked against 2000 random `±1` sequences of matched length. Ranks:
877, 1210, 224, 1246, 1012, 1681, 29, 1498 out of 2000 — no direction.

**Graded honestly: `[SCOPED NULL — ONE statistic, LOW POWER]`.** Object: the reduced sign sequence on
`Q₆`. Class of observable: max-Fourier concentration over `Q₆` only. Power: **weak** — `|Q₆|` ranges
5→138, sizes at which this statistic sees very little. Scope: 8 primes, `p ≤ 823`, `y²=x³+7`.
**This does NOT close the residual.** Multiplicative correlations, subgroup-restricted sums, and any
higher-order structure are untouched. The structure demonstrated is in the **forcing**; the residual
merely showed nothing to this one weak probe.

## 3. Item 4 — the sweep, reported as individually-verified items, not as a count

Two passes. Loose detector (dismissal adjacent to a measured positive, no scope): **513 passages,
219 files.** Tight detector (a dismissal *verdict* applied to an object, adjacent to a measured
number, no scope language, meta-files excluded): **85 passages.**

**Neither number is a finding.** The project's own lesson is that token counts measure a proxy; the
object is the passage. I read **~28 individually**. What they show:

| read | verdict |
|---|---|
| `cm_imprint_ramified_prime_findings.md` (`freq(3∣n_t)=0.762` vs generic `½`, secp's curve) | **positive, well stated, controlled — not buried** |
| `cm_divisibility_dependence_findings.md` (reversal law 24/24, non-CM control shows nothing) | **positive, controlled — not buried** |
| `RESULT_joint_shadow_decompose_v2.md` "Untested — do NOT conclude all generic" (μ3/GLV frequency support) | flagged **and followed up** (`PREREG_harmonic_support_pattern`, `RESULT_mu6_isotype_leak_structure`, `RESULT_joint_shadow_mu3`) |
| `ANALYSIS_n1_cap_anew_channel_kronecker_route_v1.md` *"this whole route is dead"* | already caught — the same file's D-2 refutes its own falsifier, and `ANALYSIS_n1_charpoly_collapse_v1.md` §0 records it |
| `KNOWN_FACTS_*` *"carries no per-key input"* | PRNG/generation side — **out of scope by standing rule**, not a lead |
| `POSITIVE_FINDINGS_ADDENDUM_1_v1.md:413` *"generic in BOTH norms"* | carries its own sup-norm control |
| `POSITIVE_FINDINGS_ADDENDUM_2_v1.md:120` *"generic-rate ~4–6% in BOTH strata"* | rate given, two strata — scoped |
| **`RESULT_joint_shadow_decompose_v2.md` "Flagged sub-observation (not banked)"** | **the one genuine unclosed item — §1 above, now closed** |

**Finding: 1 genuine unclosed item in ~28 read, plus my own burial today (§2).**

**Honest limit:** 28 of 85 tight candidates read. This is a **sample**, not an exhaustive audit. I
cannot say the answer is one. I can say the sample shows no graveyard.

## 4. The conclusion that matters

**The record is better at this than I was today.** Prior sessions wrote the warning *and* discharged
it — the one item they left open, they had explicitly labelled "not banked" with the exact test it
needed. The burial pattern is concentrated in **live session reasoning**, not in the accumulated
artifacts.

Every catch today came from a mechanical device — a built-in `Σ = 0` validity check (twice, on the
#26 test), a firing control, the `experiment-designer` gate, a plant. **None came from noticing.**
The operative fix is therefore not vigilance: **a dismissal must produce an artifact before it is
allowed to stand.**
