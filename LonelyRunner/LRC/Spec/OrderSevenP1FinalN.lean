import LonelyRunner.LRC.Spec.OrderSevenU5FinalN
import LonelyRunner.LRC.Spec.OrderSevenP1RootN
import LonelyRunner.LRC.Spec.OrderSevenP1Zdom0N
import LonelyRunner.LRC.Spec.OrderSevenP1Zdom1N
import LonelyRunner.LRC.Spec.OrderSevenP1Zdom2N
import LonelyRunner.LRC.Spec.OrderSevenP1Zdom3N
import LonelyRunner.LRC.Spec.OrderSevenP1Zdom4N
import LonelyRunner.LRC.Spec.OrderSevenP1Zdom5N
import LonelyRunner.LRC.Spec.OrderSevenP1Zdom6N

/-!
# AbsP1 proved

`absP1 : LRC.O7Abs.AbsP1`: runner 1, three unit abstract states and one valuation-1 abstract state share an
instant.  The valuation-1 state's good instants contain a base set `UB b` (`zdom_all`); the three units contain
table states (`wit_of`); `Claim (UB b) 3` from the certificate.  No `sorry`, no `native_decide`.
-/

namespace LRC.O7U5
open LRC.O7Abs

theorem zdom_all {T : Nat} (hT : T < 49) {gi ri : Nat} (hg : gi < 12) (hr : ri < 6) :
    ∃ b, b < 252 ∧ ∀ x, x < 210 → (UB b).testBit x = true →
      ok T (fvecs.getD gi []) (7 * (ri + 1)) (inst x).1 (inst x).2 := by
  interval_cases T
  · exact zdom_of zdomP0 hg hr
  · exact zdom_of zdomP1 hg hr
  · exact zdom_of zdomP2 hg hr
  · exact zdom_of zdomP3 hg hr
  · exact zdom_of zdomP4 hg hr
  · exact zdom_of zdomP5 hg hr
  · exact zdom_of zdomP6 hg hr
  · exact zdom_of zdomP7 hg hr
  · exact zdom_of zdomP8 hg hr
  · exact zdom_of zdomP9 hg hr
  · exact zdom_of zdomP10 hg hr
  · exact zdom_of zdomP11 hg hr
  · exact zdom_of zdomP12 hg hr
  · exact zdom_of zdomP13 hg hr
  · exact zdom_of zdomP14 hg hr
  · exact zdom_of zdomP15 hg hr
  · exact zdom_of zdomP16 hg hr
  · exact zdom_of zdomP17 hg hr
  · exact zdom_of zdomP18 hg hr
  · exact zdom_of zdomP19 hg hr
  · exact zdom_of zdomP20 hg hr
  · exact zdom_of zdomP21 hg hr
  · exact zdom_of zdomP22 hg hr
  · exact zdom_of zdomP23 hg hr
  · exact zdom_of zdomP24 hg hr
  · exact zdom_of zdomP25 hg hr
  · exact zdom_of zdomP26 hg hr
  · exact zdom_of zdomP27 hg hr
  · exact zdom_of zdomP28 hg hr
  · exact zdom_of zdomP29 hg hr
  · exact zdom_of zdomP30 hg hr
  · exact zdom_of zdomP31 hg hr
  · exact zdom_of zdomP32 hg hr
  · exact zdom_of zdomP33 hg hr
  · exact zdom_of zdomP34 hg hr
  · exact zdom_of zdomP35 hg hr
  · exact zdom_of zdomP36 hg hr
  · exact zdom_of zdomP37 hg hr
  · exact zdom_of zdomP38 hg hr
  · exact zdom_of zdomP39 hg hr
  · exact zdom_of zdomP40 hg hr
  · exact zdom_of zdomP41 hg hr
  · exact zdom_of zdomP42 hg hr
  · exact zdom_of zdomP43 hg hr
  · exact zdom_of zdomP44 hg hr
  · exact zdom_of zdomP45 hg hr
  · exact zdom_of zdomP46 hg hr
  · exact zdom_of zdomP47 hg hr
  · exact zdom_of zdomP48 hg hr

theorem absP1 : AbsP1 := by
  intro T2 g2 ρ2 T3 g3 ρ3 T4 g4 ρ4 Tz gz ρz h2 h3 h4 hTz hgz hρz h7 h0
  obtain ⟨k2, hk2, w2⟩ := wit_of h2
  obtain ⟨k3, hk3, w3⟩ := wit_of h3
  obtain ⟨k4, hk4, w4⟩ := wit_of h4
  obtain ⟨gi, hgi, rfl⟩ := fvec_index hgz
  have hri : ρz = 7 * (ρz / 7 - 1 + 1) := by omega
  obtain ⟨b, hb, wz⟩ := zdom_all hTz hgi (show ρz / 7 - 1 < 6 by omega)
  obtain ⟨x, hx, hUx, hks⟩ := p1_all blkSpec capSpec clsSpec.1 clsSpec.2 hb [k2, k3, k4] rfl
    (by intro k hk; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> assumption)
  obtain ⟨r1, hc1, hc6⟩ := r1_of r1P hx
  refine ⟨(inst x).1, (inst x).2, hc1, hc6, r1, w2 x hx (hks k2 (by simp)), w3 x hx (hks k3 (by simp)),
    w4 x hx (hks k4 (by simp)), ?_⟩
  rw [hri]; exact wz x hx hUx

end LRC.O7U5
