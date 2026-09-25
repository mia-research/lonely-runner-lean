"""Hand edits for the §5 port; appends the Case 5.1 dispatcher and the §5 top level."""
import re,sys
p=sys.argv[1]; s=open(p).read()
SRC=open('/home/user/lrc-n8-lean/LonelyRunner/LRC/Spec/OrderSixSecFiveN.lean').read()
def block(start,end):
    i=SRC.index(start); j=SRC.index(end,i); return SRC[i:j]
main=block('theorem bhk_s5_case51_main','\n\n\n')
main=main.replace("""  -- Indirect form: suppose the runners cover every time within `1/6` of the
  -- origin, and derive a contradiction (BHK's `B₀ = ℝ⁺`).
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ t, ∃ i, circDist (vᵢ t) < 1/6` — the covering assumption.
""","""  -- Each branch ends at a named lonely instant (`Found speeds`).
""")
main=main.replace(' hsmall hcon k D',' hsmall k D')
main=main.replace("""      obtain ⟨i, l, hil, h30, h33⟩ := bhk_s5_case51_config_bounds speeds hmono hpos
        hsmall k D hk3 hD hkD h511 h512
      exact bhk_s5_case51_x4_incompatible _ i l hil h30 h33""","""      obtain hF | ⟨i, l, hil, h30, h33⟩ := bhk_s5_case51_config_bounds speeds hmono hpos
        hsmall k D hk3 hD hkD h511 h512
      · exact hF
      exact (bhk_s5_case51_x4_incompatible _ i l hil h30 h33).elim""")
assert 'hcon' not in main, main
docmain='''/-- **BHK §5, Case 5.1** (`v₁ = k D`, `k ≥ 3`) at a named instant: Case 5.1.1, Case 5.1.2,
    or the generic configuration, each ending at the instant its lemmas name. -/
'''
k3=block('theorem bhk_s5_k_ge_3','\n\n/--')
s5=block('/-- **Window extraction.**','\n\nend LRC')
tail='\n'+docmain+main+'\n\n/-- **BHK §5, Case 5.1.** -/\n'+k3+'\n\n'+s5+'\n\n'
i=s.index('end LRC.OrderSixN.S7.Named')
s=s[:i]+tail+s[i:]
def rep(a,b,c=1):
    global s
    assert s.count(a)==c,(s.count(a),a[:120]); s=s.replace(a,b)
# a 1234-gap: read on the named gap [a, b]
rep('''  intro s hs
  obtain hF | ⟨i, hi⟩ := found_or_blocked speeds s
  · exact Or.inl hF
  right
  fin_cases i''','''  rcases found_or_blocked_on speeds (Set.Icc a b) with hF | hblk
  · exact Or.inl hF
  right
  intro s hs
  obtain ⟨i, hi⟩ := hblk s hs
  fin_cases i''')
# a long 1234-gap: a point of it outside runner 5's zone is the instant
rep('''  block_length_bound speeds ⟨4, by omega⟩ (hpos _) a b hab
    (bhk_s5_case51_gap1234_subset speeds hgap)
''','''by
  rw [or_iff_not_imp_right]
  intro hlong
  obtain ⟨τ, hτ, hτ5⟩ := Set.not_subset.mp
    (fun hsub => hlong (block_length_bound speeds ⟨4, by omega⟩ (hpos _) a b hab hsub))
  rw [mem_unsafeOf_iff, not_lt] at hτ5
  refine ⟨τ, fun i => ?_⟩
  fin_cases i
  · exact hgap τ hτ 0
  · exact hgap τ hτ 1
  · exact hgap τ hτ 2
  · exact hgap τ hτ 3
  · exact hτ5
''')
s=s.replace(') :=\nby\n',') := by\n')
open(p,'w').write(s)
print('ok')
