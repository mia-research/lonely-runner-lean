#!/usr/bin/env python3
"""Certificate C (Lean): five units and one valuation-1 runner (exactly one multiple of 7, valuation 1).
Core OrderSevenL2CCoreN: level-2 masks mask2 i (bit j iff GridOK 2 (unit49 j) (unit49 i)), the 240 failing sorted
normalised index tuples failL, chunkC1 (every sorted (w2..w5) either shares a level-2 bit with unit 1 or is failing),
chunkC2 p (failing tuple #p: every lift x in (0..6)^4 and class t: level-3 masks of 1 and the lifts and mmL3 t share a
bit).  Parts OrderSevenL2CP{g}N.  Usage: o7_l2C_lean_v1.py PER_MODULE outdir"""
import sys
per, outdir = int(sys.argv[1]), sys.argv[2]
u49 = [u for u in range(1, 49) if u % 7]
m2 = []
for u in u49:
    m = 0
    for j, k in enumerate(u49):
        if 7 <= (u * k) % 49 <= 42: m |= 1 << j
    m2.append(m)
F = [(a, b, c, d) for a in range(42) for b in range(a, 42) for c in range(b, 42) for d in range(c, 42)
     if (m2[0] & m2[a] & m2[b] & m2[c] & m2[d]) == 0]
core = f'''import LonelyRunner.LRC.Spec.OrderSevenL3BCoreN

/-!
# Order seven, certificate C: exactly one multiple of 7, of valuation 1, and five units

Level 2 for the units unless their sorted normalised residues mod 49 are one of the 240 failing tuples `failL`; for those,
level 3 with every lift mod 343 and every class of the multiple's cofactor.  Generator:
`experiments/n7_native/cascade/o7_l2C_lean_v1.py`.
-/

namespace LRC.O7L3
open LRC.O7Grid

def mask2Tab : Array ℕ := #[{", ".join(map(str, m2))}]

def mask2 (i : ℕ) : ℕ := mask2Tab.getD i 0

def failL : List (ℕ × ℕ × ℕ × ℕ) := [{", ".join(f"({a}, {b}, {c}, {d})" for a, b, c, d in F)}]

def chunkC1 : Bool :=
  allR 42 0 fun a => let x := mask2 0 &&& mask2 a
    allR (42 - a) a fun b => let y := x &&& mask2 b
      allR (42 - b) b fun c => let z := y &&& mask2 c
        allR (42 - c) c fun d => (z &&& mask2 d) != 0 || failL.contains (a, b, c, d)

def idx343 (v : ℕ) : ℕ := v - 1 - v / 7

def chunkC2 (p : ℕ) : Bool :=
  let f := failL.getD p (0, 0, 0, 0)
  allR 7 0 fun x2 => allR 7 0 fun x3 => allR 7 0 fun x4 => allR 7 0 fun x5 =>
    let m := maskL3 0 &&& maskL3 (idx343 (unit49 f.1 + 49 * x2)) &&& maskL3 (idx343 (unit49 f.2.1 + 49 * x3)) &&&
      maskL3 (idx343 (unit49 f.2.2.1 + 49 * x4)) &&& maskL3 (idx343 (unit49 f.2.2.2 + 49 * x5))
    allR 42 0 fun t => (m &&& mmL3 t) != 0

end LRC.O7L3
'''
open(f"{outdir}/OrderSevenL2CCoreN.lean", "w").write(core)
open(f"{outdir}/OrderSevenL2C1N.lean", "w").write('''import LonelyRunner.LRC.Spec.OrderSevenL2CCoreN

/-! Order seven certificate C1: the level-2 table with its failing tuples (kernel-checked). -/

namespace LRC.O7L3

theorem chunkC1_ok : chunkC1 = true := by decide +kernel

end LRC.O7L3
''')
mods = [list(range(i, min(i + per, len(F)))) for i in range(0, len(F), per)]
for g, ps in enumerate(mods):
    thms = "\n".join(f"theorem chunkC2_{p} : chunkC2 {p} = true := by decide +kernel" for p in ps)
    open(f"{outdir}/OrderSevenL2CP{g}N.lean", "w").write(f'''import LonelyRunner.LRC.Spec.OrderSevenL2CCoreN

/-! Order seven certificate C2, part {g}: failing tuples {ps[0]}..{ps[-1]}. -/

namespace LRC.O7L3

{thms}

end LRC.O7L3
''')
print(f"C: {len(F)} failing tuples, {len(mods)} C2 modules")
