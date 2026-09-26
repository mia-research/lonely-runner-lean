"""Generate LonelyRunner/LRC/Spec/DoubledSlotN.lean: the constant cases of the doubled-slot family, each band checked
exactly here before the proof line is emitted."""
from fractions import Fraction as F
from math import floor
END = {1: (F(1, 16), 2), 2: (F(25, 56), 7), 3: (F(17, 56), 7), 4: (F(9, 40), 5), 5: (F(3, 16), 2), 6: (F(9, 56), 7)}
FAR = {1: F(9, 64), 2: F(9, 56), 3: F(3, 16), 4: F(9, 40), 5: F(17, 56), 6: F(25, 56), 7: F(1, 16)}
def band(lo, hi):
    """integer N with N + 1/8 <= lo and hi <= N + 7/8, or None"""
    N = floor(lo - F(1, 8))
    return N if N + F(1, 8) <= lo and hi <= N + F(7, 8) else None
def rat(x): return f"({x.numerator}/{x.denominator} : ℝ)" if x.denominator != 1 else f"({x.numerator} : ℝ)"
L = []
# end cases: reading a in 1..7, a != cc, at homeEndT cc m
for cc, (t0, dd) in END.items():
    for a in range(1, 8):
        if a == cc: continue
        N0 = band(a * t0, a * t0); N1 = band(a * t0, a * (t0 + F(1, 64 * dd)))
        assert N0 is not None and N1 is not None and N0 == N1, (cc, a)
        ifs = "".join(f"if_neg (show ({cc} : ℕ) ≠ {j} by norm_num), " for j in range(1, cc) if j <= 5)
        sel = f"if_pos rfl" if cc <= 5 else ""
        rw = f"rw [homeEndT, {ifs}{sel}]" if cc <= 5 else f"rw [homeEndT, {ifs.rstrip(', ')}]"
        L.append(f"""theorem end_{cc}_{a} (m : ℕ) (hm : 1 ≤ m) (x : ℤ) (hx : x = {a}) :
    (8 : ℝ)⁻¹ ≤ circDist ((x : ℝ) * homeEndT {cc} m) := by
  subst hx
  {rw}
  split_ifs with hd
  · have hmin : ({dd} : ℝ) ≤ m := by exact_mod_cast Nat.le_of_dvd (by omega) hd
    have h0 : (0 : ℝ) ≤ 1 / (64 * (m : ℝ)) := by positivity
    have h1 : 1 / (64 * (m : ℝ)) ≤ 1 / (64 * {dd}) :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    apply LRC.TwoPinner.clear_of_band (N := {N0}) <;> push_cast <;> linarith
  · apply LRC.TwoPinner.clear_of_band (N := {N0}) <;> norm_num
""")
# far exceptions: s = 0, m = 1, far member at 8; readings a = i - 8, i in 0..7, i != r
for r, t in FAR.items():
    for i in range(8):
        if i == r: continue
        a = i - 8; N = band(a * t, a * t); assert N is not None, (r, a)
        ifs = ", ".join(f"if_neg (show ({r} : ℕ) ≠ {j} by norm_num)" for j in range(1, r) if j <= 6)
        tail = ", if_pos rfl" if r <= 6 else ""
        rw = f"rw [farEx{', ' + ifs if ifs else ''}{tail}]"
        L.append(f"""theorem fx_{r}_{-a} (x : ℤ) (hx : x = {a}) : (8 : ℝ)⁻¹ ≤ circDist ((x : ℝ) * farEx {r}) := by
  subst hx
  {rw}
  apply LRC.TwoPinner.clear_of_band (N := {N}) <;> norm_num
""")
ends = " | ".join(f"exact end_{cc}_{a} m hm _ (by omega)" for cc in END for a in range(1, 8) if a != cc)
fars = " | ".join(f"exact fx_{r}_{8 - i} _ (by omega)" for r in FAR for i in range(8) if i != r)
open("gen_doubled_slot_cases.lean.txt", "w").write("\n".join(L))
open("gen_doubled_slot_first.txt", "w").write(ends + "\n" + fars + "\n")
print(len(L), "generated lemmas; all bands checked")
