# Dropped-Unit Thin-Burden Chain: Scan Analysis

Date: 2026-04-12
Status: empirical diagnostic note

## 1. Scan Summary

Script: `tools/transfer_depth_scan_v1.py`
Scope: all dropped-unit Case-2 gcd-1 tuples with full coverage at b_0

| n | max_speed | tuples | fully covered b_0 | depth 0 | depth 1 | depth > 1 |
|---|-----------|--------|-------------------|---------|---------|-----------|
| 5 |  15       |   846  |       147         |  147    |    0    |     0     |
| 6 |  18       |  3630  |       675         |  642    |   33    |     0     |
| 7 |  14       |  2073  |       420         |  416    |    4    |     0     |
| 8 |  16       |  6960  |      1152         | 1113    |   39    |     0     |

**Key result: max chain depth = 1 in all scanned cases. Zero depth-2+ cases.**

Depth -1 (not shown) = tuples not fully covered at b_0, not in the "fully covered" count.

## 2. Depth-1 Cases: n=7 (prime), E_non = {2,6,8,9,10}

Representative case: E = (2,6,7,8,9,10), n=7, L=2520, b_0=360.
Missing unit classes: d ∈ {4,5}. Initial thin residue: r*=1, sole cover: runner 6.

### Trace of thin-burden chain

At b_0=360:
- Runner 6 (ρ=6, q=0): bad = {0, 1}  ← r*=1 is HIGH element
- Runner 2 (ρ=2, q=0): bad = {0, 3}
- Runner 8 (ρ=1, q=1): bad = {5, 6}
- Runner 9 (ρ=2, q=1): bad = {3, 6}
- Runner 10 (ρ=3, q=1): bad = {2, 4}

Multiplicities: 0→2, 1→1(thin!), 2→1(thin), 3→2, 4→1(thin), 5→1(thin), 6→2.

Step 1 (b=420, runner 6 floor 0→1):
  bad changes {0,1} → {1,2}. Residue 0 drops (still covered by runner 2). Residue 2 enters.
  r*=1 persists (HIGH of floor 0 → LOW of floor 1).

Step 2 (b=756, runner 10 floor 2→3):
  bad changes {4,6} → {6,1}. Residue 4 drops. Residue 1 enters as HIGH element.
  Now both runners 6 AND 10 cover r*=1 (multiplicity 2).

Step 3 (b=840, runner 6 floor 1→2):
  bad changes {1,2} → {2,3}. Residue 1 drops from runner 6.
  r*=1 sole cover: runner 10 (transfer recorded at b=840). ← CHAIN DEPTH 1

After transfer (b=840+):
  Runner 10 at floor 3 covers {6, 1}.
  Multiplicities: 0→1, 1→1(thin), 2→2, 3→2, 4→1(thin), 5→2, 6→1(thin).
  Both r*=1 AND companion residue 6 have sole cover: runner 10.

Step 4 (b=1008, runner 10 floor 3→4):
  bad changes {6,1} → {1,3}. Residue 6 drops (LOW element). Residue 3 enters.
  r*=1 persists (HIGH of floor 3 → LOW of floor 4).
  Residue 6 now uncovered. SAFE FIBRE. ←

First safe fibre: b ≡ 6 (mod 7) in [1008, next_event). Specifically b=1013.

### Mechanism revealed

After the burden transfer from runner 6 to runner 10:
- Runner 10 is now the SOLE COVER of BOTH r*=1 AND companion residue 6
- Runner 10's next floor-reset (floor 3→4) drops the LOW element = residue 6
- Residue 6 has no other coverage → EXPOSED

The safe fibre is at residue 6 (not at r*=1, which persists in runner 10's bad set).

## 3. Structural Insight

The depth-1 mechanism has a universal pattern:

1. At b_0, thin residue r* is solely covered by runner e*
2. Runner e*'s bad set = {r*, r_c} (r_c = companion)
3. At some floor-reset event before e* drops r*, another runner e'' acquires r* (as new HIGH element)
4. r* multiplicity temporarily = 2
5. At e*'s next floor-reset, r* drops from e*, becomes sole cover of e''
6. At this point: e'''s bad set = {r**, r*} for some r**
   - r** is typically the LOW element, r* is HIGH
   - If r** also has sole cover e'': DOUBLE THIN
7. At e'''s next floor-reset: LOW element r** drops → exposed (unless another runner acquires it)

In all 4 bounded n=7 depth-1 cases: step 7 produces a safe fibre directly.
In all 416 bounded n=7 depth-0 cases: step 5 directly produces exposure.

## 4. Implications for CT.1

The empirical bound "chain depth ≤ 1" suggests:

**Conjecture CT.1-depth-1 (empirically verified):** For all n ∈ {5,6,7,8} and speeds ≤ 2n or 3n (as appropriate), the thin-burden chain has depth ≤ 1. Hence the safe fibre appears at either:
- The first floor-reset event of e* that drops r* (depth 0), or
- The first floor-reset event of the sole-cover transfer runner e'' that drops the companion residue (depth 1)

**Key open question:** Can depth > 1 occur for larger speeds or larger n? If not, what structural property prevents it?

**Proposed mechanism for depth-1 bound:** After one transfer, runner e'' becomes sole cover of both r* (HIGH) and a companion r** (LOW). At e'''s next reset, r** drops. For r** to be re-covered (preventing depth 2 termination), a THIRD runner e''' must acquire r** at the SAME floor-reset event. This requires e'' and e''' to share a coincident floor-reset, which is an arithmetic coincidence not seen in bounded data.

## 5. Files

- Scan script: `tools/transfer_depth_scan_v1.py`
- n=8 prototype proof: `reports/dropped_unit_transport_instability_proof_attempt_2026-04-12.md`
- n=7 depth-1 detail: see §2 of this file
