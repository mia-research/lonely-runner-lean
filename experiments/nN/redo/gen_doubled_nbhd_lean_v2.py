"""Generate the case lemmas of DoubledNbhdN.lean (ends and far exceptions), every band checked in exact arithmetic
against the worst-case error the Lean proof uses.  Shifted end readings on a band edge at delta' = 0 are proved by
the edge argument: the reading clears the edge by a*delta' = a/(64m), and 4 t0 eta <= delta' since eta <= 1/(256 m)."""
from fractions import Fraction as F
from math import floor, gcd
def R(x): return f"({x.numerator} / {x.denominator} : ℝ)" if x.denominator != 1 else f"({x.numerator} : ℝ)"
def Nof(x):
    N = floor(x - F(1, 8))
    assert N + F(1, 8) <= x <= N + F(7, 8), x
    return N
END = {1: (2, 0), 2: (7, 3), 3: (7, 2), 4: (5, 1), 5: (6, 1), 6: (7, 1)}
FARFL = {1: (0, 1), 2: (1, 1), 3: (2, 1), 4: (3, 1), 5: (1, 2), 6: (1, 3), 7: (6, 0)}
DJ = lambda s, r, m, j: f"((dsZ {s} {r} {m} ⟨{j}, by norm_num⟩ - dsZ {s} {r} {m} ⟨{s}, by norm_num⟩ : ℤ) : ℝ)"
out = []
for s in (0, 7):
    for r in range(1, 7):
        cc = r if s == 0 else 7 - r
        d, N0 = END[cc]; P = 8 * N0 + 1; c0 = F(P, 8 * d)
        g = gcd(P, d); dd = d // g; Pr = P // g; Kc = Pr
        x0 = d if s == 0 else 7 - d; DX = x0 - s
        emax_s = F(1, 256 * (dd + 1)); dmax = F(1, 64 * dd)
        mq = f"({dd} * q)"
        L = [f"""theorem end_{s}_{r} {{δ : Fin 8 → ℝ}} {{m : ℕ}} (hm : 1 ≤ m) {{η : ℝ}} (hη0 : 0 ≤ η)
    (hηm : η * (256 * ((m : ℝ) + 1)) ≤ 1)
    (hδ : ∀ j, |δ j - ((dsZ {s} {r} m j - dsZ {s} {r} m ⟨{s}, by norm_num⟩ : ℤ) : ℝ)| ≤ η) :
    ∃ t : ℝ, 0 < t ∧ ∀ j : Fin 8, j ≠ ⟨{s}, by norm_num⟩ → (8 : ℝ)⁻¹ ≤ circDist (δ j * t) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hη1 : η ≤ 1 / 512 := by nlinarith
  have hηm' : η * m ≤ 1 / 256 := by nlinarith
  by_cases hdv : {dd} ∣ m
  · obtain ⟨q, rfl⟩ := hdv
    have hq : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
    have hmq : (({dd} * q : ℕ) : ℝ) = {dd} * (q : ℝ) := by push_cast; ring
    have hη2 : η ≤ {R(emax_s)} := by
      have : η * (256 * ((({dd} * q : ℕ) : ℝ) + 1)) ≤ 1 := hηm
      rw [hmq] at this; nlinarith
    have hηδ : η ≤ 1 / (64 * ({dd} * (q : ℝ))) / 4 := by
      have : η * (256 * ((({dd} * q : ℕ) : ℝ) + 1)) ≤ 1 := hηm
      rw [hmq] at this
      rw [div_div, le_div_iff₀ (by positivity)]; nlinarith
    set X : Fin 8 := ⟨{r}, by norm_num⟩
    have hDX : ((dsZ {s} {r} {mq} X - dsZ {s} {r} {mq} ⟨{s}, by norm_num⟩ : ℤ) : ℝ) = 8 * ({dd} * (q : ℝ)) := by
      simp [X, dsZ]
    have hDX1 : 1 ≤ |((dsZ {s} {r} {mq} X - dsZ {s} {r} {mq} ⟨{s}, by norm_num⟩ : ℤ) : ℝ)| := by
      rw [hDX, abs_of_pos (show (0 : ℝ) < 8 * ({dd} * (q : ℝ)) by nlinarith)]; nlinarith
    have hδX0 := LRC.DoubledNbhd.nz_of (by linarith) (hδ X) hDX1
    set t0 : ℝ := (8 * ({Kc} * (q : ℝ)) + 1) / (64 * ({dd} * (q : ℝ))) with ht0def
    have ht0pos : 0 < t0 := by rw [ht0def]; apply div_pos <;> nlinarith
    have ht0c : t0 = {R(c0)} + 1 / (64 * ({dd} * (q : ℝ))) := by rw [ht0def]; field_simp; ring
    have hδ' : 0 ≤ 1 / (64 * ({dd} * (q : ℝ))) ∧ 1 / (64 * ({dd} * (q : ℝ))) ≤ {R(dmax)} := by
      constructor
      · apply div_nonneg (by norm_num); nlinarith
      · rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]; nlinarith
    have ht0η : t0 * η ≤ {R(c0 + dmax)} * {R(emax_s)} :=
      mul_le_mul (by rw [ht0c]; linarith [hδ'.2]) hη2 hη0 (by norm_num)
    have ht0le1 : t0 ≤ 1 := by rw [ht0c]; linarith [hδ'.2]
    have ht0η1 : t0 * η ≤ η := mul_le_of_le_one_left hη0 ht0le1
    refine ⟨t0 * ((dsZ {s} {r} {mq} X - dsZ {s} {r} {mq} ⟨{s}, by norm_num⟩ : ℤ) : ℝ) / δ X, ?_, ?_⟩
    · exact LRC.DoubledNbhd.pos_reloc ht0pos (by linarith) (hδ X) hDX1
    intro j hj
    fin_cases j"""]
        for j in range(8):
            if j == s:
                L.append("    · exact absurd rfl hj"); continue
            if j == r:
                L.append(f"""    · refine LRC.DoubledNbhd.flank_exact (L := (({Kc} * q : ℕ) : ℤ)) hδX0 (Or.inl ?_)
      rw [hDX, ht0def]; push_cast; field_simp; ring"""); continue
            a = j - s; N = Nof(a * c0)
            err = (c0 + dmax) * 4 * emax_s
            lo_edge = (a * c0 == N + F(1, 8)); hi_edge = (a * c0 == N + F(7, 8))
            lo_const = min(a * c0, a * (c0 + dmax)) - err >= N + F(1, 8)
            hi_const = max(a * c0, a * (c0 + dmax)) + err <= N + F(7, 8)
            if lo_const: lo_tac = "linarith [ht0η, hδ'.1, hδ'.2, e]"
            else:
                assert lo_edge and a > 0 and a * (c0 + dmax) >= a * c0, (s, r, j)
                lo_tac = "linarith [ht0η1, hηδ, hδ'.1, e]"
            if hi_const: hi_tac = "linarith [ht0η, hδ'.1, hδ'.2, e]"
            else:
                assert hi_edge and a < 0, (s, r, j)
                hi_tac = "linarith [ht0η1, hηδ, hδ'.1, e]"
            L.append(f"""    · have hj' := hδ ⟨{j}, by norm_num⟩
      have hDj : {DJ(s, r, mq, j)} = {a} := by simp [dsZ]
      have e : t0 * ({a} : ℝ) = {a} * {R(c0)} + {a} * (1 / (64 * ({dd} * (q : ℝ)))) := by rw [ht0c]; ring
      apply LRC.DoubledNbhd.reloc_clear (N := {N}) (K := 1) ht0pos.le hη0 (by linarith) (hδ X) hDX1 hj'
        (by norm_num)
      · rw [hDj, hDX, abs_of_pos (show (0 : ℝ) < 8 * ({dd} * (q : ℝ)) by nlinarith)]; norm_num; nlinarith
      · rw [hDj]; {lo_tac}
      · rw [hDj]; {hi_tac}""")
        L.append(f"""  · set X : Fin 8 := ⟨{x0}, by norm_num⟩
    have hDX : ((dsZ {s} {r} m X - dsZ {s} {r} m ⟨{s}, by norm_num⟩ : ℤ) : ℝ) = {DX} := by simp [X, dsZ]
    have hDX1 : 1 ≤ |((dsZ {s} {r} m X - dsZ {s} {r} m ⟨{s}, by norm_num⟩ : ℤ) : ℝ)| := by rw [hDX]; norm_num
    have hδX0 := LRC.DoubledNbhd.nz_of (by linarith) (hδ X) hDX1
    set t0 : ℝ := {R(c0)} with ht0def
    refine ⟨t0 * ((dsZ {s} {r} m X - dsZ {s} {r} m ⟨{s}, by norm_num⟩ : ℤ) : ℝ) / δ X, ?_, ?_⟩
    · exact LRC.DoubledNbhd.pos_reloc (by norm_num) (by linarith) (hδ X) hDX1
    intro j hj
    fin_cases j""")
        for j in range(8):
            if j == s:
                L.append("    · exact absurd rfl hj"); continue
            if j == x0:
                L.append(f"""    · refine LRC.DoubledNbhd.flank_exact (L := {N0}) hδX0 ({'Or.inl' if DX > 0 else 'Or.inr'} ?_)
      rw [hDX, ht0def]; norm_num"""); continue
            if j == r:
                errp = c0 * (F(2, 512) + F(16, 256) / d); assert errp <= F(1, dd) - F(1, 8), (s, r)
                L.append(f"""    · have hj' := hδ ⟨{r}, by norm_num⟩
      have hDj : {DJ(s, r, 'm', r)} = 8 * (m : ℝ) := by simp [dsZ]
      exact LRC.DoubledNbhd.partner_lip (m := m) (dd := {dd}) (P' := {Pr}) (dX := {d}) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by rw [ht0def]; norm_num) hdv hη0 hη1 hηm' (by rw [hDX]; norm_num)
        (by norm_num) (by rw [ht0def]; norm_num) (hδ X) hj' hDj"""); continue
            a = j - s; err = c0 * (2 * F(1, 512) + 2 * F(1, 512) * 4)
            N = Nof(a * c0); assert N + F(1, 8) + err <= a * c0 and a * c0 + err <= N + F(7, 8), (s, r, j)
            L.append(f"""    · have hj' := hδ ⟨{j}, by norm_num⟩
      have hDj : {DJ(s, r, 'm', j)} = {a} := by simp [dsZ]
      apply LRC.DoubledNbhd.reloc_clear (N := {N}) (K := 4) (by norm_num) hη0 (by linarith) (hδ X) hDX1 hj'
        (by norm_num)
      · rw [hDj, hDX]; norm_num
      · rw [hDj, ht0def]; linarith
      · rw [hDj, ht0def]; linarith""")
        out.append("\n".join(L) + "\n")
for r, (j0, Lp) in FARFL.items():
    DX = j0 - 8; t0 = F(8 * Lp + 1, 8 * abs(DX))
    L = [f"""theorem farx_{r} {{δ : Fin 8 → ℝ}} {{η : ℝ}} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 512)
    (hδ : ∀ j, |δ j - ((dsZ 0 {r} 1 j - dsZ 0 {r} 1 ⟨{r}, by norm_num⟩ : ℤ) : ℝ)| ≤ η) :
    ∃ t : ℝ, 0 < t ∧ ∀ j : Fin 8, j ≠ ⟨{r}, by norm_num⟩ → (8 : ℝ)⁻¹ ≤ circDist (δ j * t) := by
  set X : Fin 8 := ⟨{j0}, by norm_num⟩
  have hDX : ((dsZ 0 {r} 1 X - dsZ 0 {r} 1 ⟨{r}, by norm_num⟩ : ℤ) : ℝ) = {DX} := by simp [X, dsZ]
  have hDX1 : 1 ≤ |((dsZ 0 {r} 1 X - dsZ 0 {r} 1 ⟨{r}, by norm_num⟩ : ℤ) : ℝ)| := by rw [hDX]; norm_num
  have hδX0 := LRC.DoubledNbhd.nz_of (by linarith) (hδ X) hDX1
  set t0 : ℝ := {R(t0)} with ht0def
  refine ⟨t0 * ((dsZ 0 {r} 1 X - dsZ 0 {r} 1 ⟨{r}, by norm_num⟩ : ℤ) : ℝ) / δ X, ?_, ?_⟩
  · exact LRC.DoubledNbhd.pos_reloc (by norm_num) (by linarith) (hδ X) hDX1
  intro j hj
  fin_cases j"""]
    for j in range(8):
        if j == r: L.append("  · exact absurd rfl hj"); continue
        if j == j0:
            L.append(f"""  · refine LRC.DoubledNbhd.flank_exact (L := {Lp}) hδX0 (Or.inr ?_)
    rw [hDX, ht0def]; norm_num"""); continue
        a = j - 8; err = t0 * (2 * F(1, 512) + 2 * F(1, 512) * 8)
        N = Nof(a * t0); assert N + F(1, 8) + err <= a * t0 and a * t0 + err <= N + F(7, 8), (r, j)
        L.append(f"""  · have hj' := hδ ⟨{j}, by norm_num⟩
    have hDj : ((dsZ 0 {r} 1 ⟨{j}, by norm_num⟩ - dsZ 0 {r} 1 ⟨{r}, by norm_num⟩ : ℤ) : ℝ) = {a} := by simp [dsZ]
    apply LRC.DoubledNbhd.reloc_clear (N := {N}) (K := 8) (by norm_num) hη0 (by linarith) (hδ X) hDX1 hj'
      (by norm_num)
    · rw [hDj, hDX]; norm_num
    · rw [hDj, ht0def]; linarith
    · rw [hDj, ht0def]; linarith""")
    out.append("\n".join(L) + "\n")
HEAD = '''import LonelyRunner.LRC.Spec.DoubledNbhdCoreN

/-!
# The deviated doubled slot: the end cases and the far member's exceptions (generated)

Generated by `experiments/nN/redo/gen_doubled_nbhd_lean_v2.py`; every band checked there in exact arithmetic against
the worst-case error used here, and re-checked by Lean.  No `sorry`, no `native_decide`.
-/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace LRC.DoubledNbhd

open LRC.DoubledSlot

'''
open("../../../LonelyRunner/LRC/Spec/DoubledNbhdCasesN.lean", "w").write(HEAD + "\n".join(out) + "\nend LRC.DoubledNbhd\n")
print(len(out), "case lemmas written; all bands checked")
