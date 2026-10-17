#!/usr/bin/env python3
"""Certificate B (Lean): four units and one valuation-1 runner 7 m' are in band at a common level-3 unit instant.
Core OrderSevenL3BCoreN: unit49 list (42 units mod 49), masks mmL3 t (bit j iff GridOK 2 (unitL3 j) (unit49 t)), and
chunkB3 i2 lo3 hi3 = for i3 in [lo3, hi3), i4 >= i3: for all t < 42: mask(0)&mask(i2)&mask(i3)&mask(i4)&mmL3 t != 0.
Parts OrderSevenL3BP{g}N, balanced by (#(i3,i4) pairs * 42).  Usage: o7_l3B_lean_v1.py TARGET outdir"""
import sys
TARGET, outdir = int(sys.argv[1]), sys.argv[2]
units = [u for u in range(1, 343) if u % 7]
u49 = [u for u in range(1, 49) if u % 7]
mm = []
for t in u49:
    m = 0
    for j, k in enumerate(units):
        if 7 <= (t * k) % 49 <= 42: m |= 1 << j
    mm.append(m)
n = 294
core = f'''import LonelyRunner.LRC.Spec.OrderSevenL3SpecN

/-!
# Order seven, level 3, certificate B: four units and one valuation-1 runner

`unit49 t` is the `t`-th unit mod 49 (`t < 42`); bit `j` of `mmL3 t` is set iff `GridOK 2 (unitL3 j) (unit49 t)`
(the valuation-1 runner `7 · unit49 t` at the level-3 instant `unitL3 j`).  `chunkB3 i2 lo3 hi3` checks every sorted
`i3 ∈ [lo3, hi3)`, `i4 ≥ i3` against all 42 classes.  Generator: `experiments/n7_native/cascade/o7_l3B_lean_v1.py`.
-/

namespace LRC.O7L3
open LRC.O7Grid

def unit49Tab : Array ℕ := #[{", ".join(map(str, u49))}]

def unit49 (t : ℕ) : ℕ := unit49Tab.getD t 0

def mmTab : Array ℕ := #[
  {",\n  ".join(map(str, mm))}]

def mmL3 (t : ℕ) : ℕ := mmTab.getD t 0

def chunkB3 (i2 lo3 hi3 : ℕ) : Bool :=
  let a := maskL3 0 &&& maskL3 i2
  allR (hi3 - lo3) lo3 fun i3 => let b := a &&& maskL3 i3
    allR ({n} - i3) i3 fun i4 => let c := b &&& maskL3 i4
      allR 42 0 fun t => (c &&& mmL3 t) != 0

end LRC.O7L3
'''
open(f"{outdir}/OrderSevenL3BCoreN.lean", "w").write(core)
def it3(i3): return (n - i3) * 42
pieces = []
for i2 in range(n):
    lo3 = i2; acc = 0
    for i3 in range(i2, n):
        acc += it3(i3)
        if acc >= TARGET or i3 == n - 1:
            pieces.append((i2, lo3, i3 + 1, acc)); lo3 = i3 + 1; acc = 0
mods = []; cur = []; acc = 0
for p in pieces:
    if cur and acc + p[3] > TARGET: mods.append(cur); cur = []; acc = 0
    cur.append(p); acc += p[3]
if cur: mods.append(cur)
for g, ps in enumerate(mods):
    thms = "\n".join(f"theorem chunkB3_{p[0]}_{p[1]} : chunkB3 {p[0]} {p[1]} {p[2]} = true := by decide +kernel" for p in ps)
    open(f"{outdir}/OrderSevenL3BP{g}N.lean", "w").write(f'''import LonelyRunner.LRC.Spec.OrderSevenL3BCoreN

/-! Order seven level-3 certificate B, part {g}: {len(ps)} pieces, {sum(p[3] for p in ps)} checks. -/

namespace LRC.O7L3

{thms}

end LRC.O7L3
''')
open("o7_l3B_pieces.txt", "w").write("\n".join(f"{p[0]} {p[1]} {p[2]} {p[3]}" for p in pieces) + "\n")
open("o7_l3B_mods.txt", "w").write(str(len(mods)) + "\n")
print(f"B: {len(pieces)} pieces, {len(mods)} modules, total checks {sum(p[3] for p in pieces)}")
