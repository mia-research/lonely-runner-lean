#!/usr/bin/env python3
"""Generate the Lean level-3 certificate (A): five units mod 343 lonely on the level-3 unit grid.
Core module OrderSevenL3CoreN: unit list (index -> unit), the 294 level-3 masks (bit j of mask i set iff
GridOK 3 (unit j) (unit i)), `allR`, and `chunkA lo hi` = for i2 in [lo, hi), i3 in [i2, 294), i4 in [i3, 294),
i5 in [i4, 294): mask(0) & mask(i2) & mask(i3) & mask(i4) & mask(i5) != 0  (unit #0 = 1).
Part modules OrderSevenL3AP{g}N prove chunkA lo hi = true by decide +kernel, balanced by iteration count.
Usage: o7_l3_lean_v1.py TARGET_ITERS outdir"""
import sys
from math import comb
TARGET, outdir = int(sys.argv[1]), sys.argv[2]
N = 343
units = [u for u in range(1, N) if u % 7]
masks = []
for u in units:
    m = 0
    for j, k in enumerate(units):
        if 49 <= (u * k) % N <= 294: m |= 1 << j
    masks.append(m)
n = len(units)
core = f'''import LonelyRunner.LRC.Spec.OrderSevenLevel2N

/-!
# Order seven, level 3: unit list, masks and the chunk check (certificate A)

`unitL3 i` is the `i`-th unit mod 343 (`i < 294`, `unitL3 0 = 1`); bit `j` of `maskL3 i` is set iff
`GridOK 3 (unitL3 j) (unitL3 i)` (`maskL3_spec`, kernel-checked).  `chunkA lo hi` checks, for every sorted index tuple
`lo ≤ i2 < hi`, `i2 ≤ i3 ≤ i4 ≤ i5 < 294`, that the five masks of `0, i2, i3, i4, i5` share a bit.
Generator: `experiments/n7_native/cascade/o7_l3_lean_v1.py`.
-/

namespace LRC.O7L3
open LRC.O7Grid

def unitTab : Array ℕ := #[{", ".join(map(str, units))}]

def unitL3 (i : ℕ) : ℕ := unitTab.getD i 0

def maskTab : Array ℕ := #[
  {",\n  ".join(map(str, masks))}]

def maskL3 (i : ℕ) : ℕ := maskTab.getD i 0

def allR : ℕ → ℕ → (ℕ → Bool) → Bool
  | 0, _, _ => true
  | n + 1, i, f => f i && allR n (i + 1) f

theorem allR_spec : ∀ (n i : ℕ) (f : ℕ → Bool), allR n i f = true → ∀ j, i ≤ j → j < i + n → f j = true
  | 0, i, f, _, j, h1, h2 => by omega
  | n + 1, i, f, h, j, h1, h2 => by
    simp only [allR, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
    · exact h.1
    · exact allR_spec n (i + 1) f h.2 j h1' (by omega)

/-- fixed `i2`, `i3` in `[lo3, hi3)` (with `i3 ≥ i2`), then `i4 ≥ i3`, `i5 ≥ i4` -/
def chunkA3 (i2 lo3 hi3 : ℕ) : Bool :=
  let a := maskL3 0 &&& maskL3 i2
  allR (hi3 - lo3) lo3 fun i3 => let b := a &&& maskL3 i3
    allR ({n} - i3) i3 fun i4 => let c := b &&& maskL3 i4
      allR ({n} - i4) i4 fun i5 => (c &&& maskL3 i5) != 0

def chunkA (lo hi : ℕ) : Bool :=
  allR (hi - lo) lo fun i2 => chunkA3 i2 i2 {n}

theorem chunkA_spec {{lo hi : ℕ}} (h : chunkA lo hi = true) {{i2 i3 i4 i5 : ℕ}} (h2 : lo ≤ i2) (h2' : i2 < hi)
    (h3 : i2 ≤ i3) (h4 : i3 ≤ i4) (h5 : i4 ≤ i5) (h5' : i5 < {n}) :
    (maskL3 0 &&& maskL3 i2 &&& maskL3 i3 &&& maskL3 i4 &&& maskL3 i5) ≠ 0 := by
  have a := allR_spec _ _ _ h i2 h2 (by omega)
  simp only [chunkA3] at a
  have b := allR_spec _ _ _ a i3 h3 (by omega)
  have c := allR_spec _ _ _ b i4 h4 (by omega)
  have d := allR_spec _ _ _ c i5 h5 (by omega)
  simpa using d

end LRC.O7L3
'''
open(f"{outdir}/OrderSevenL3CoreN.lean", "w").write(core)
def it3(i3): return comb(n - i3 + 1, 2)      # sorted (i4, i5) in [i3, n)
pieces = []                                  # (i2, lo3, hi3, iters)
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
    thms = "\n".join(f"theorem chunkA3_{p[0]}_{p[1]} : chunkA3 {p[0]} {p[1]} {p[2]} = true := by decide +kernel" for p in ps)
    open(f"{outdir}/OrderSevenL3AP{g}N.lean", "w").write(f'''import LonelyRunner.LRC.Spec.OrderSevenL3CoreN

/-! Order seven level-3 certificate A, part {g}: {len(ps)} pieces, {sum(p[3] for p in ps)} sorted tuples. -/

namespace LRC.O7L3

{thms}

end LRC.O7L3
''')
open("o7_l3_pieces.txt", "w").write("\n".join(f"{p[0]} {p[1]} {p[2]} {p[3]}" for p in pieces) + "\n")
open("o7_l3_mods.txt", "w").write("\n".join(" ".join(f"{p[0]}:{p[1]}:{p[2]}" for p in ps) for ps in mods) + "\n")
print(f"{n} units; total sorted tuples {sum(p[3] for p in pieces)}; {len(pieces)} pieces; {len(mods)} modules")
