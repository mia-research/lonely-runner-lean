#!/usr/bin/env python3
"""Half-unit certificates (band symmetry u <-> 7^a - u).  Indices 0..146 of the level-3 unit list are the units
1..171; indices 0..20 of the mod-49 unit list are the units 1..24.
  A: for sorted i2 <= i3 <= i4 <= i5 < 147: maskL3 0 & maskL3 i2 & ... & maskL3 i5 != 0
  B: for sorted i2 <= i3 <= i4 < 147 and t < 21: maskL3 0 & ... & maskL3 i4 & mmL3 t != 0
  C1: for sorted a <= b <= c <= d < 21 (mod-49 half indices): level-2 masks of 0,a,b,c,d share a bit, or the tuple is in
      failH; C2: for each failH tuple and lifts x in (0..6)^4 and t < 21: level-3 masks of 1 and the lifts
      unit49 f_i + 49 x_i and mmL3 t share a bit.
Writes OrderSevenHalfCoreN, parts OrderSevenHalfAP{g}N / HalfBP{g}N / HalfCP{g}N, balanced at TARGET checks."""
import sys
TARGET, outdir = int(sys.argv[1]), sys.argv[2]
from math import comb
u49 = [u for u in range(1, 49) if u % 7]
m2 = []
for u in u49:
    m = 0
    for j, k in enumerate(u49):
        if 7 <= (u * k) % 49 <= 42: m |= 1 << j
    m2.append(m)
H2 = 21; H3 = 147
FH = [(a, b, c, d) for a in range(H2) for b in range(a, H2) for c in range(b, H2) for d in range(c, H2)
      if (m2[0] & m2[a] & m2[b] & m2[c] & m2[d]) == 0]
core = f'''import LonelyRunner.LRC.Spec.OrderSevenL3BCoreN

/-!
# Order seven, half-unit certificates (band symmetry `u ↔ 7^a − u`)

Indices `0..146` of `unitL3` are the units `1..171`; indices `0..20` of `unit49` are the units `1..24`.  Since a speed and
its negative are in band at the same instants, it suffices to check these halves.
Generator: `experiments/n7_native/cascade/o7_half_lean_v1.py`.
-/

namespace LRC.O7L3
open LRC.O7Grid

def chunkAH (i2 lo3 hi3 : ℕ) : Bool :=
  let a := maskL3 0 &&& maskL3 i2
  allR (hi3 - lo3) lo3 fun i3 => let b := a &&& maskL3 i3
    allR ({H3} - i3) i3 fun i4 => let c := b &&& maskL3 i4
      allR ({H3} - i4) i4 fun i5 => (c &&& maskL3 i5) != 0

def chunkBH (i2 lo3 hi3 : ℕ) : Bool :=
  let a := maskL3 0 &&& maskL3 i2
  allR (hi3 - lo3) lo3 fun i3 => let b := a &&& maskL3 i3
    allR ({H3} - i3) i3 fun i4 => let c := b &&& maskL3 i4
      allR {H2} 0 fun t => (c &&& mmL3 t) != 0

def mask2Tab : Array ℕ := #[{", ".join(map(str, m2))}]

def mask2 (i : ℕ) : ℕ := mask2Tab.getD i 0

def failH : List (ℕ × ℕ × ℕ × ℕ) := [{", ".join(f"({a}, {b}, {c}, {d})" for a, b, c, d in FH)}]

def chunkC1 : Bool :=
  allR {H2} 0 fun a => let x := mask2 0 &&& mask2 a
    allR ({H2} - a) a fun b => let y := x &&& mask2 b
      allR ({H2} - b) b fun c => let z := y &&& mask2 c
        allR ({H2} - c) c fun d => (z &&& mask2 d) != 0 || failH.contains (a, b, c, d)

def idx343 (v : ℕ) : ℕ := v - 1 - v / 7

def chunkC2 (p : ℕ) : Bool :=
  let f := failH.getD p (0, 0, 0, 0)
  allR 7 0 fun x2 => allR 7 0 fun x3 => allR 7 0 fun x4 => allR 7 0 fun x5 =>
    let m := maskL3 0 &&& maskL3 (idx343 (unit49 f.1 + 49 * x2)) &&& maskL3 (idx343 (unit49 f.2.1 + 49 * x3)) &&&
      maskL3 (idx343 (unit49 f.2.2.1 + 49 * x4)) &&& maskL3 (idx343 (unit49 f.2.2.2 + 49 * x5))
    allR {H2} 0 fun t => (m &&& mmL3 t) != 0

end LRC.O7L3
'''
open(f"{outdir}/OrderSevenHalfCoreN.lean", "w").write(core)
def build(tag, fn, per_i3, nmax_i2):
    pieces = []
    for i2 in range(nmax_i2):
        lo3 = i2; acc = 0
        for i3 in range(i2, H3):
            acc += per_i3(i3)
            if acc >= TARGET or i3 == H3 - 1:
                pieces.append((i2, lo3, i3 + 1, acc)); lo3 = i3 + 1; acc = 0
    mods = []; cur = []; acc = 0
    for p in pieces:
        if cur and acc + p[3] > TARGET: mods.append(cur); cur = []; acc = 0
        cur.append(p); acc += p[3]
    if cur: mods.append(cur)
    for g, ps in enumerate(mods):
        thms = "\n".join(f"theorem {fn}_{p[0]}_{p[1]} : {fn} {p[0]} {p[1]} {p[2]} = true := by decide +kernel" for p in ps)
        open(f"{outdir}/OrderSevenHalf{tag}P{g}N.lean", "w").write(f'''import LonelyRunner.LRC.Spec.OrderSevenHalfCoreN

/-! Order seven half-unit certificate {tag}, part {g}: {len(ps)} pieces, {sum(p[3] for p in ps)} checks. -/

namespace LRC.O7L3

{thms}

end LRC.O7L3
''')
    open(f"o7_half_{tag}_pieces.txt", "w").write("\n".join(f"{p[0]} {p[1]} {p[2]} {p[3]}" for p in pieces) + "\n")
    return len(pieces), len(mods), sum(p[3] for p in pieces)
print("A:", build("A", "chunkAH", lambda i3: comb(H3 - i3 + 1, 2), H3))
print("B:", build("B", "chunkBH", lambda i3: (H3 - i3) * H2, H3))
per = max(1, TARGET // (2401 * H2))
mods = [list(range(i, min(i + per, len(FH)))) for i in range(0, len(FH), per)]
for g, ps in enumerate(mods):
    thms = "\n".join(f"theorem chunkC2_{p} : chunkC2 {p} = true := by decide +kernel" for p in ps)
    open(f"{outdir}/OrderSevenHalfCP{g}N.lean", "w").write(f'''import LonelyRunner.LRC.Spec.OrderSevenHalfCoreN

/-! Order seven half-unit certificate C2, part {g}: failing tuples {ps[0]}..{ps[-1]}. -/

namespace LRC.O7L3

{thms}

end LRC.O7L3
''')
open(f"{outdir}/OrderSevenHalfC1N.lean", "w").write('''import LonelyRunner.LRC.Spec.OrderSevenHalfCoreN

/-! Order seven half-unit certificate C1 (kernel-checked). -/

namespace LRC.O7L3

theorem chunkC1_ok : chunkC1 = true := by decide +kernel

end LRC.O7L3
''')
print(f"C: {len(FH)} failing half tuples, {len(mods)} C2 modules, {len(FH) * 2401 * H2} checks")
open("o7_half_counts.txt", "w").write(f"{len(FH)} {len(mods)}\n")
