"""Hand edits applied after convert.py (exact-text replacements; each must hit)."""
import re,sys
p=sys.argv[1]; s=open(p).read()
def rep(old,new,count=1):
    global s
    n=s.count(old)
    assert n==count,(n,old[:120])
    s=s.replace(old,new)

# --- gap covering on a named gap [a, b] -------------------------------------------------
rep("""  intro s hs
  obtain hF | ⟨i, hi⟩ := found_or_blocked w s
  · exact Or.inl hF
  right
  fin_cases i""","""  rcases found_or_blocked_on w (Set.Icc a b) with hF | hblk
  · exact Or.inl hF
  right
  intro s hs
  obtain ⟨i, hi⟩ := hblk s hs
  fin_cases i""")
rep("""  intro s hs
  rcases found6_or_blocked w s with hF | ⟨i, hi⟩ | hfict
  · exact Or.inl hF
  right
  · fin_cases i""","""  rcases found6_or_blocked_on w (Set.Icc a b) with hF | hblk
  · exact Or.inl hF
  right
  intro s hs
  rcases hblk s hs with ⟨i, hi⟩ | hfict
  · fin_cases i""")

# --- Lemma 12: the gap and its translates by multiples of 1/g are read first -------------
for six in (False,True):
    F='found6_or_blocked_on' if six else 'found_or_blocked_on'
    gc='bhk_prop11_gap_covered2 w hgap h0safe' if six else 'bhk_prop11_gap_covered w hgap'
    head="""  by_cases h4 : Set.Icc a b ⊆ unsafeOf w ⟨3, by omega⟩
  · exact Or.inl h4
  by_cases h5 : Set.Icc a b ⊆ unsafeOf w ⟨4, by omega⟩
  · exact Or.inr (Or.inl h5)
  refine Or.inr (Or.inr ?_)
  obtain hF | hcov45 := """+gc+"""
  · exact Or.inl hF
  right
"""
    newhead="""  obtain hF | hcov45 := """+gc+"""
  · exact Or.inl hF
  rcases """+F+""" w {τ | ∃ p ∈ Set.Icc a b, ∃ i : ℕ, τ = p + (i : ℝ) * (1 / g)} with hF | hblkT
  · exact Or.inl hF
  right
  by_cases h4 : Set.Icc a b ⊆ unsafeOf w ⟨3, by omega⟩
  · exact Or.inl h4
  by_cases h5 : Set.Icc a b ⊆ unsafeOf w ⟨4, by omega⟩
  · exact Or.inr (Or.inl h5)
  refine Or.inr (Or.inr ?_)
"""
    rep(head,newhead)
rep("""    obtain hF | ⟨k, hk⟩ := found_or_blocked w (p + (i : ℝ) * (1 / g))
    · exact Or.inl hF
""","""    obtain ⟨k, hk⟩ := hblkT _ ⟨p, hp, i, rfl⟩
""")
rep("""    rcases found6_or_blocked w (p + (i : ℝ) * (1 / g)) with hF | ⟨k, hk⟩ | hfict
    · exact Or.inl hF
    · fin_cases k""","""    rcases hblkT _ ⟨p, hp, i, rfl⟩ with ⟨k, hk⟩ | hfict
    · fin_cases k""")

# --- the diagonal span bound: a point of [a, b] clear of runner 5 is the instant ---------
for six in (False,True):
    blk=re.search(r'(lemma bhk_diag_sbound'+('2' if six else '')+r' .*?\n)  rw \[or_iff_not_imp_right\]\n.*?\n\n',s,re.S)
    sig=blk.group(1)
    fin="""  rw [or_iff_not_imp_right]
  intro hcon
  push_neg at hcon
  -- a point of `[a, b]` outside runner 5's zone: every runner is clear there
  obtain ⟨τ, hτ, hτ4⟩ := Set.not_subset.mp
    (bhk_prop11_not_subset_unsafeOf w ⟨4, by omega⟩ (hpos _) hab hcon)
  rw [mem_unsafeOf_iff, not_lt] at hτ4
  refine ⟨τ, fun i => ?_""" + (", hfic τ hτ⟩" if six else "⟩") + """
  fin_cases i
  · exact h0 τ hτ
  · exact h1 τ hτ
  · exact h2 τ hτ
  · exact h3 τ hτ
  · exact hτ4

"""
    s=s[:blk.start()]+sig+fin+s[blk.end():]

# --- the unconditional forms: Lemma 13 first ---------------------------------------------
for nm,callee in (('bhk_prop11_v4_lt_2v3_uncond','bhk_prop11_v4_lt_2v3'),('bhk_prop11_lemma17_uncond','bhk_prop11_lemma17')):
    rep(f"""  {callee} w hmono hpos hsum hsmall
    (bhk_prop11_lemma13 w hmono hpos hsum hsmall)""",f"""by
  rcases bhk_prop11_lemma13 w hmono hpos hsum hsmall with hF | hq5
  · exact Or.inl hF
  exact {callee} w hmono hpos hsum hsmall hq5""")
open(p,'w').write(s)
print('patched')
s=s.replace(') :=\nby\n',') := by\n')
# --- part 2's window form is replaced by the statements below -----------------------------
i=s.index('/-- **Proposition 11 — indirect core (part 2).**')
j=s.index('end LRC.OrderSixN.S7.Named')
s=s[:i]+'''/-- **Proposition 11, part 1, at a named instant** (BHK pp. 17–40). Integer speeds
    `w₀ < ⋯ < w₄` with `w₀ + w₁ = w₂` and `3 w₀ < w₂` have a time at which every runner is
    `≥ 1/6` from the origin. The instant is the one `bhk_prop11_core` names. -/
theorem bhk_prop11_part1 (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩) :
    ∃ t : ℝ, ∀ i, circDist ((w i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  obtain ⟨t, ht⟩ := bhk_prop11_core w hmono hpos hsum hsmall
  exact ⟨t, ht⟩

/-- **Proposition 11, part 2, at a named instant.** Under `6 w₀ < w₂` the instant can be
    chosen with `{w₀ t} ∉ (5/12, 7/12)`: it is the instant `bhk_prop11_core2_cover6` names,
    at which the fictional runner `2 w₀` is also clear. -/
theorem bhk_prop11_part2 (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩) :
    ∃ t : ℝ, (∀ i, circDist ((w i : ℝ) * t) ≥ (1 : ℝ) / 6) ∧
      Int.fract ((w ⟨0, by omega⟩ : ℝ) * t) ∉ Set.Ioo (5/12 : ℝ) (7/12) := by
  obtain ⟨t, ht, h0⟩ := bhk_prop11_core2_cover6 w hmono hpos hsum hsmall6
  exact ⟨t, ht, fun hwin => absurd (bhk_prop11_fict_window hwin) (not_lt.mpr h0)⟩

'''+s[j:]
open(p,'w').write(s)
print('final theorems in')
