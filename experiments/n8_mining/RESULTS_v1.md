# RESULTS v1 — n = 8 extension of the Theorem 5.2 / Conjecture 5.2-H mining scan

Run against `PREREG_v1.md`, 2026-09-07. Artefacts: `run_n8_scan_v1.py`, `cells_v1.py`,
`n8_scan_v1.csv` (258 814 rows), `n8_rows.pkl`.

**Scope tag — attaches to every n = 8 number below.**
`[n=8 | speeds ∈ 1..10 | k_G ∈ 1..6, k_A ∈ 1..6 | p prime ≤ 19 | gcd(p,L_G)=1 | p < n·L_G
| I_G, I_A ≠ ∅ | p ∉ G∪A | primitive | no M cap]`
Control numbers carry the control's own tag `[n ≤ 7 | speeds ∈ 1..8 | k_G ≤ 3, k_A ≤ 2 |
p ≤ 19 | M ≤ 5·10⁶]` and are never placed in a column with n = 8 numbers without both tags.

---

## The cell that fired: CELL C

> **Theorem 5.2-P discharges 65 807 of 66 044 n = 8 LRC-shape inputs on [scope tag]; the
> remaining 237 require direct verification, which was performed — `N_joint ≥ 10` for all
> 237. Conjecture 5.2-H therefore holds on this scope by 5.2-P ∪ direct check, exactly as at
> n ≤ 7.**

On the `DELTA0` stratum: 69 134 of 69 387 discharged, 253 residual, `N_joint ≥ 8` for all.

### Residual characterisation (pre-registered; not a count alone)

| | n ≤ 7 control | n = 8 |
|---|---|---|
| stratum size (`DI ∪ ModDI`) | 5 517 | 66 044 |
| pigeonhole residuals | 53 (0.961%) | **237 (0.359%)** |
| `p` histogram | {2:30, 3:21, 5:1, 7:1} | {2:109, 3:95, 5:14, 7:19} |
| `lrc_class` | {ModDI:34, DI:19} | {ModDI:233, DI:4} |
| `targets_all_missed_LA` | {0:53} | {0:237} |
| `target_in_missed_LA` | {0:52, 1:1} | {0:237} |
| `N_joint` minimum | 2 | 10 |
| `(k_G,k_A)` | — | {(2,5):10, (3,4):78, (4,3):104, (5,2):41, (6,1):4} |
| `cIG` range | — | 22 … 1026 |

Two comparisons, stated as shape comparisons with no verdict beyond them, per Cell C:

- **The residual rate does not rise with `n`.** 0.359% at n = 8 against 0.961% at n ≤ 7 —
  and per-`n` in the control, 0.321% (n=4), 1.237% (n=5), 0.874% (n=6). The
  pre-registered reading "Theorem 5.2-P weakens with `n`" required `R/N` to exceed the
  n ≤ 7 rate by more than an order of magnitude. **It does not; that reading is not
  licensed.** n = 7 contributes 0 LRC-shape inputs to the control (see §PREREG 0), so the
  series is n ∈ {4,5,6,8}.
- **The `DI` share of residuals falls**, 19/53 = 36% to 4/237 = 1.7%. Reported; no
  mechanism claimed.
- **The mechanism split is unchanged.** All residuals at both `n` have
  `targets_all_missed_LA = 0`; the Stage-1 mechanism accounts for none of them at either
  `n`. (Checked in the control rather than assumed from the counterexample signature.)

Mandatory nested slices, one run:

| slice | N (strict) | pigeonhole residuals | counterexamples |
|---|---|---|---|
| speeds ≤ 8 | 4 122 | 12 (0.291%) | 0 |
| speeds ≤ 9 | 19 464 | 59 (0.303%) | 0 |
| speeds ≤ 10 | 66 044 | 237 (0.359%) | 0 |

---

## CELL A — does not fire

`#{LRC-shape ∧ N_joint = 0} = 0` on both strata (66 044 and 69 387 inputs). No
counterexample to Conjecture 5.2-H in its own stated scope was found on [scope tag].

The zero is informative only because planted control **P2** fires: forcing the smallest
known counterexample (`n=3, G=[3], A=[1,5], p=2`) through the LRC-shape branch does make
Cell A fire, so this is an empirical zero and not an unreachable branch.

## CELL B — does not fire

237 (strict) / 253 (`DELTA0`) inputs fail the pigeonhole, so the claim "Theorem 5.2-P alone
discharges the scanned n = 8 LRC-shape space" is **not** available. Cell C governs.

## CELL D — sub-cell D3 (vacuous)

> **The δ-discriminator of Remark 5.2-V is UNTESTED at n = 8 on [scope tag]: the δ ≥ 1
> stratum (67 144 rows, matching the pre-committed count) yielded 0 counterexamples, so the
> n ≤ 7 δ-separation is neither confirmed nor refuted here.**

`N_joint = 0` occurs **nowhere** in the n = 8 scan — 0 of 258 814 rows across
δ ∈ [−5, +3]. For comparison the control has 681, distributed δ ∈ {1:69, 2:333, 3:279},
and by `n`: 531 (n=3), 145 (n=4), 5 (n=5), 0 (n=6), 0 (n=7, no inputs). The counterexample
class was already empty at n = 6 in the control's scope. δ ≥ 4 is unexamined (hole H1).

This is explicitly **not** "the discriminator holds at n = 8".

## CELL E — must-not-fire; did not fire

0 rows with `pigeon = True ∧ N_joint = 0`, at n = 8 and in the control. Assertion live in
the runner (`run_n8_scan_v1.py` stage 3) and shown live by planted control P4.

---

## Controls, quoted

Matched control, re-executed in-process before n = 8 was touched, 9.6 s:

```
total 38664 OK | CE 681 OK | pigeon_all 34825 OK | CE_with_pigeon 0 OK
strict 5517 OK | strict_pigeon 5464 OK | strict_resid 53 OK
delta0 8388 OK | delta0_resid 83 OK
CE delta-histogram      {1: 69, 2: 333, 3: 279}   expected {1:69,2:333,3:279}
53-residual p-histogram {2: 30, 3: 21, 5: 1, 7: 1} expected {2:30,3:21,5:1,7:1}
```

Planted controls: **P1** fires (`N_joint=0`, `n_band_betas=12`, `cIA=1`, `n·L_A=15`,
`slack=−2`, `targets_all_missed_LA=1`); **P2** fires; **P3** fires; **P4** fires.

## Declared deviation from the pre-registration

PREREG §6.3 requires the n = 8 run to use the control's code path.
`compute_residue_structure` walks each band element by element at cost `|I_G|·L_A·p`;
`fast_residue_structure` computes the band's β-image as the contiguous cyclic run it is,
in O(1) per α. **The deviation is not accepted on that argument**: both implementations were
run over all 38 664 control inputs with **0 field mismatches on any row**, and a
deterministic 1-in-500 sample of the n = 8 scan (518 inputs) was re-checked against the
reference, also with no mismatch. Scan wall time 37 s against the spec's ~59 min estimate.

## Observed maxima (PREREG §4.3 requires measured, not estimated)

`L_G` 2520, `L_A` 2520, `n·L_A` 20 160, `cIG` 5798, `cIA` 5798, `n_band_betas` 20 160,
`M` 22 982 400.

## Holes, restated verbatim next to the numbers

**H1** speeds > 10 — Conjecture 5.2-H is for all integer speeds; nothing here bounds the
unbounded-speed case, and δ ≥ 4 needs S ≥ 11 and is entirely unexamined.
**H2** `p > 19` with `p < n·L_G` still holding.
**H3** `k_G > 6` or `k_A > 6` in the δ ≥ 1 stratum (conventional caps; irrelevant to δ = 0,
where they are forced).
**H4** composite `p` coprime to `L_G`.
**H5** `p ∈ G ∪ A` — excluded by the harness, not by Theorem 5.2; a genuine hole in the
control too.
**H6** `n ≥ 9`. **H7** `I_G = ∅` or `I_A = ∅` (correctly excluded).

## What this run does NOT license

Not that Theorem 12.1 becomes unconditional at n = 8; not that n = 8 is closed, clean, or
settled; not that the residual phenomenon is absent (237 of them are the finding); not that
the δ-discriminator holds at n = 8. Conjecture 5.2-H holds **on [scope tag]**, by
Theorem 5.2-P for 65 807 inputs and by direct verification for 237.

---

## EXPLORATORY (post-hoc, not pre-registered)

The pigeonhole **margin** degrades sharply with the speed pool, though the residual *rate*
moves little. `slack_min` over the strict stratum by maximum speed: `+2` (≤7), `−32` (≤8),
`−112` (≤9), `−922` (≤10). By prime: `p=2: −922, 3: −456, 5: −30, 7: −86`, and `p ≥ 11`
never fails (`slack_min` = 2, 4, 6, 6 at p = 11, 13, 17, 19). Only 26 inputs in the whole
stratum sit at `slack ∈ {1,2,3}`.

Read as a probe rather than a result: the pigeonhole failure is confined to `p ≤ 7` at
n = 8, and its depth grows with the pool. The registered next probe is `S ≥ 11`, which also
opens δ ≥ 4 (H1) — the only region where the δ-discriminator could be tested at n = 8.
