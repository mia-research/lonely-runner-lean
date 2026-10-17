#!/usr/bin/env python3
"""Assembly module for certificate A: for each i2, chunkA3 i2 i2 294 from its pieces (split lemma), then the full
sorted statement.  Reads o7_l3_pieces.txt / o7_l3_mods.txt (written by o7_l3_lean_v2.py)."""
import sys
outdir = sys.argv[1]
pieces = [tuple(map(int, l.split())) for l in open("o7_l3_pieces.txt") if l.strip()]
nmods = sum(1 for l in open("o7_l3_mods.txt") if l.strip())
by_i2 = {}
for i2, lo3, hi3, _ in pieces: by_i2.setdefault(i2, []).append((lo3, hi3))
imports = "\n".join(f"import LonelyRunner.LRC.Spec.OrderSevenL3AP{g}N" for g in range(nmods))
lines = []
for i2 in range(294):
    ps = by_i2[i2]
    assert ps[0][0] == i2 and ps[-1][1] == 294
    if len(ps) == 1:
        lines.append(f"theorem full_{i2} : chunkA3 {i2} {i2} 294 = true := chunkA3_{i2}_{ps[0][0]}")
    else:
        # combine left to right: chunkA3 i2 i2 h_k = true by induction over pieces
        steps = [f"theorem full_{i2} : chunkA3 {i2} {i2} 294 = true := by"]
        cur_hi = ps[0][1]
        steps.append(f"  have h0 : chunkA3 {i2} {i2} {cur_hi} = true := chunkA3_{i2}_{ps[0][0]}")
        for t, (lo3, hi3) in enumerate(ps[1:], 1):
            steps.append(f"  have h{t} : chunkA3 {i2} {i2} {hi3} = true := by")
            steps.append(f"    rw [chunkA3_split (by norm_num : {i2} ≤ {lo3}) (by norm_num : {lo3} ≤ {hi3}), h{t-1}, chunkA3_{i2}_{lo3}]; rfl")
        steps.append(f"  exact h{len(ps) - 1}")
        lines.append("\n".join(steps))
fulls = ", ".join(f"full_{i2}" for i2 in range(294))
src = f'''{imports}
import LonelyRunner.LRC.Spec.OrderSevenL3SpecN

/-!
# Order seven, level 3: certificate A assembled

`chunkA_all`: for every sorted index tuple `i2 ≤ i3 ≤ i4 ≤ i5 < 294`, the masks of unit `1` and the four units share a bit.
-/

namespace LRC.O7L3

theorem chunkA3_split {{i2 lo mid hi : ℕ}} (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    chunkA3 i2 lo hi = (chunkA3 i2 lo mid && chunkA3 i2 mid hi) := by
  unfold chunkA3
  rw [show hi - lo = (mid - lo) + (hi - mid) by omega, allR_append, show lo + (mid - lo) = mid by omega]

{chr(10).join(lines)}

theorem chunkA_all : chunkA 0 294 = true := by
  unfold chunkA
  simp only [allR, Nat.sub_zero, {fulls}, Bool.and_true]

end LRC.O7L3
'''
open(f"{outdir}/OrderSevenL3AN.lean", "w").write(src)
print("pieces", len(pieces), "modules", nmods)
