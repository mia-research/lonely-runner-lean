import Fresh.FourBlockLongTailExit

/-! Native reference episode with every original reading retained. The
closed initial grid edge isolates; otherwise three forced setters lead to
the exact exit-or-continuation face. No original visit toT is asserted. -/
namespace Fresh.FourBlockLongTailEpisode
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockLongTailBounds Fresh.FourBlockLongTailPhase
  Fresh.FourBlockLongTailThirdMove Fresh.FourBlockLongTailExit

theorem native_episode (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j) (m a b e : ℤ)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4) :
    let E := disparitySet (speeds c g h j p q r) 0
    (remainder g h j m a b e=7/8 ∧ LonelyAt E ((m : ℝ)+1/8)) ∨
    ((7/8 : ℝ) < remainder g h j m a b e ∧
      IsMove E ((m : ℝ)+1/8) (outerOpening g h j m a b e) ∧
      IsMove E (outerOpening g h j m a b e) (packetOpening g h j m a b e 1) ∧
      IsMove E (packetOpening g h j m a b e 1) (packetOpening g h j m a b e 2) ∧
      (g+h+j+8*remainder g h j m a b e ≤ 9 → LonelyAt E (packetOpening g h j m a b e 2)) ∧
      (¬g+h+j+8*remainder g h j m a b e ≤ 9 →
        IsMove E (packetOpening g h j m a b e 2) (packetOpening g h j m a b e 3))) := by
  dsimp only
  rcases left_reference_choice c g h j p q r hp hq hr (by omega) hgpos hhpos hjpos m a b e hg hh hj hsum with hclear|⟨hcap,hfirst⟩
  · exact Or.inl hclear
  · have hsecond := Fresh.FourBlockEndpointSecondMove.unit_partner_next_move c g h j p q r hp hq hr (by omega)
      hgpos hhpos hjpos m a b e hg hh hj hsum hcap
    have hsecond' : IsMove (disparitySet (speeds c g h j p q r) 0)
        (outerOpening g h j m a b e) (packetOpening g h j m a b e 1) := by
      simpa only [first_partner_eq] using hsecond
    obtain ⟨hexit,hcont⟩ := exit_or_continue c g h j p q r hp hq hr hs hgpos hhpos hjpos m a b e hg hh hj hsum
    exact Or.inr ⟨hcap,hfirst,hsecond',third_move c g h j p q r hp hq hr hs hgpos hhpos hjpos m a b e hg hh hj hsum,hexit,hcont⟩

#print axioms native_episode
end Fresh.FourBlockLongTailEpisode
