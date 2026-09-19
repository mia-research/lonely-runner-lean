# Audit: which hypotheses are the category's, and which are mine

Prompted by the right question — when something fails to generalise, is that the problem's
requirement or a requirement I added to make a proof go through? Two of mine were found and
removed.

Lean: `experiments/n8/Derestricted_v1.lean` (3 theorems, 0 errors, axiom-clean).
Scripts: `hypothesis_audit_v1.py`, `mixed_reach_v1.py`.

---

## The audit

| theorem | hypothesis | whose? | evidence |
|---|---|---|---|
| `DivisorOrder6.profile_clear_of_order6` | `10 ≤ b` at **every** modulus | **MINE** | the per-modulus theorem needs it only at that modulus; removing it takes reach from **13.45%** to **100.00%** |
| `MinusSeven.flank_clear_of_no_tiny` | `\|d\| ≤ e` (largest flank) | **MINE** | `inWay_minus_seven` holds at any flank; only the *size form* `7\|d\| < e` needs it. Reach across all flanks 66.8% vs 29% for the size form |
| `LastClass.shadow_needs_full_denom` | every mover `0 < p < q` | **the category's** | admit `q = 1` movers or `\|ρ\| > 1` and live shadowed flanks with `max q = 2` appear |
| `SmallModuli.profile_clear_one` | every `b ≤ 9` | **the category's** | `L(b) ≥ 2` for `b ≥ 10`, so `q = 1` genuinely fails there — `clear_one_fails` proves it |
| `FirstLap.flank_clear_of_window` | `e ≤ d·A ≤ 7e` (no wraparound) | **partly mine** | sufficient, not necessary; excludes flanks that clear *by* wrapping |
| `CanonicalCandidate.small_v_clear` | `1 ≤ v ≤ 4` | **partly mine** | correct as a *uniform* statement; `v = 5,6` clear conditionally (91.6%, 85.1%) under the exact law |

## 1. The homogeneity was mine, and it cost 86.55%

`clear_of_order6` is a per-modulus theorem: given `b ≥ 10` and a candidate in the `1/6` band at
`b`, it clears `b`. Nothing about the rest of the profile enters. But `profile_clear_of_order6`
demanded `b ≥ 10` of **every** modulus — which excludes every mixed profile by fiat.

Small moduli never needed the band argument. Their blocked sets are tiny: `{0}` for `b ≤ 7`,
`{0, b-1}` for `b ∈ {8,9}`. They can be met directly.

**[PROVED — `Derestricted.profile_clear_mixed`]** A candidate clears the profile if it meets the
`1/6` band at each modulus `≥ 10` and the window directly at each modulus `< 10`. No hypothesis
on the profile's shape at all. `Derestricted.window_of_band` isolates the one place `10 ≤ b` is
genuinely needed.

**[VERIFIED — 8,000 divisor-closed profiles]** the homogeneity-bound theorems reach **13.45%**;
this reaches **100.00%**, and where it fires the candidate really clears (8,000/8,000).

**What this does and does not buy.** It removes a false restriction on *applicability* — mixed
profiles are no longer excluded by the statement. It is still a **sufficient condition on a
given `q`**, not an existence proof: at small moduli it assumes the window, which is the
conclusion there. The content remains at the large moduli. So the 100% figure measures that a
qualifying `q` always exists in the sample, not that one has been proved to exist.

## 2. The largest-flank hypothesis was mine

`MinusSeven.inWay_minus_seven` — `inWay d (8L-7) e ↔ dist(7d, 8e·ℤ) < e` — holds for **any**
flank. Only the size form `7|d| < e` requires `|d| ≤ e`, because that is where the residue is
read off without wrapping.

**[PROVED — `Derestricted.flank_clear_minus_seven`]** the `-7` opening clears a flank whenever
no difference satisfies `dist(7d, 8e·ℤ) < e`, with no hypothesis on sizes or on which flank it
is. Measured reach across all flanks is 66.8% against 29% for the size-restricted form.

## 3. Two that are genuinely the category's

`shadow_needs_full_denom` needs `0 < p < q` at every mover, and that is real: admit `q = 1`
movers (integer ratios, `p = 0`) or `|ρ| > 1` and live shadowed flanks with `max q = 2` appear
immediately. The hypothesis is not decoration.

`profile_clear_one` needs `b ≤ 9`, and `clear_one_fails` proves `q = 1` fails from `b = 10` —
the bound is exactly the reach of that candidate.

## 4. The lesson for the rest of the programme

The pattern to watch for: a **per-object** theorem wrapped in a **whole-profile** hypothesis
that the per-object theorem never needed. Both removals here are of that shape. Where a class
looks stubborn, check first whether the statement excludes it by fiat before concluding the
mathematics does.

Existence at order 8 remains open.
