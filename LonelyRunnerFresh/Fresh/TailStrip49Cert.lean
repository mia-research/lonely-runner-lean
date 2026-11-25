import Fresh.TailStrip49Cover
import Fresh.TailStrip49CertCode

/-!
# Kernel-checkable certificates for the 49–51 strip (E928)

Written 2026-11-25.  New file; nothing existing is edited.  Owner (2026-11-25): *"Try a faster restatement"*.

`TailStrip49Checked.stripCheck` is `(List.range' 1 26).all checkFirst = true`, proved by `native_decide`.  The
soundness chain in `TailStrip49Cover` uses from `cellCover` only one fact: for each accepted box, two cells
`c d` with `pairCheck box c d = true` (`pair_sound`, private there).  It never uses the search that finds them.

Here the search is moved out of the kernel.  A certificate `CertL` records the subdivision tree and, at each
leaf, the two cells as explicit numbers.  `certCheckL` re-checks only the subdivision and the pair condition.
The pair condition `pairCheckN` scans the lap range `blockers` already computes, in place of all laps `1..95`
(`checkedBlockers`); `blockers_mem` proves the narrower range still contains every blocking lap.

* `certCheckL_sound`: `certCheckL box cert = true → inBox box g → g 0 = 1 → CellPairFor g`.
* `cells_of_certs`: if every root of the strip has a certificate that checks, every normalised tuple with
  `g 5 ≤ 51` has `CellPairFor g` -- the conclusion of `cells_of_check`, without `native_decide`.
* `chunkOK` and `roots_of_chunkOK`: the bookkeeping that lets the certificates be checked in many separate
  kernel declarations.

Grades: [L] for every theorem here, and [PROVISIONAL: covering] for `cells_of_certs` and what rests on it, as for
`cells_of_check` and `tailStrip49_clearPoint`: the root boxes cover the strip and each leaf's two cells cannot both
be blocked.  The claim it supports is the strip's clear point (`tailStrip49_clearPoint`, `tailStrip49_lands`).
The search is not trusted: the certificate is data, and any certificate that passes `certCheckL` gives the
conclusion.
-/

open Classical Set

namespace Fresh.TailStrip49Cert

open Fresh Fresh.TailStrip49

/-- A certificate: the subdivision tree of `coverWith`, with the two cells of `pairCheck` at each leaf. -/
inductive CertL where
  | leaf (c d : Cell)
  | split (l r : CertL)

/-- Re-check a certificate: the same subdivision as `coverWith`, and `pairCheckN` at each leaf. -/
def certCheckL : Box → CertL → Bool
  | box, .leaf c d => pairCheckN box c d
  | box, .split l r =>
      certCheckL (left box (widest box)) l && certCheckL (right box (widest box)) r

private theorem scale_pos' : (0 : ℝ) < scale := by norm_num [scale]

/-- **The narrow blocker range is complete** [L; PROVISIONAL: covering, a step of `cells_of_certs`]: the statement of `TailStrip49Cover.blocked_mem` (private there)
with `checkedBlockers` replaced by `blockers`.  The proof is that one with two lap bounds added. -/
theorem blockers_mem {c : Cell} {lo : Nat} {x : ℝ}
    (h : windowCheck c = true) (hlo : (lo : ℝ) ≤ scale*x)
    (hmin : (minTop : ℝ) ≤ scale*x) (hmax : scale*x ≤ maxTop)
    (bad : BlocksCell x (time c.lo) (time c.hi)) :
    ∃ q ∈ blockers c lo, 0 < q.lo.d ∧ 0 < q.hi.d ∧
      q.lo.val < scale*x ∧ scale*x < q.hi.val := by
  obtain ⟨hn₀, hn₁, hd₀, hd₁, hw⟩ := window_sound h
  obtain ⟨j, hj₀, hj₁⟩ := bad
  have ha := (div_lt_iff₀ (show 0 < time c.lo by linarith [hw.1])).1 hj₀
  have hb := (lt_div_iff₀ (show 0 < time c.hi by linarith [hw.1,hw.2.1])).1 hj₁
  have hx₀ : 49 ≤ x := by norm_num [minTop,scale] at hmin; linarith
  have hx₁ : x ≤ 51 := by norm_num [maxTop,scale] at hmax; linarith
  have hh₀ : (49 : ℝ) ≤ x * time c.hi := by
    have ht : 1 ≤ time c.hi := hw.1.trans hw.2.1
    nlinarith [mul_nonneg (sub_nonneg.mpr hx₀) (sub_nonneg.mpr ht)]
  have hh₁ : x * time c.lo ≤ (765 : ℝ) := by
    have ht := hw.2.1.trans hw.2.2.1
    calc
      x * time c.lo ≤ x * 15 := mul_le_mul_of_nonneg_left ht (by linarith)
      _ ≤ 765 := by linarith
  have jlo : 1 ≤ j := by
    by_contra hbad
    have hj : (j : ℝ) ≤ 0 := by exact_mod_cast (show j ≤ 0 by omega)
    linarith
  let k := j.toNat
  have hk : (k : ℤ) = j := Int.toNat_of_nonneg (by omega)
  have hkR : (k : ℝ) = (j : ℝ) := by exact_mod_cast hk
  have hdl : (0 : ℝ) < c.lo.d := by exact_mod_cast hd₀
  have hdr : (0 : ℝ) < c.hi.d := by exact_mod_cast hd₁
  have hnl : (0 : ℝ) < c.lo.n := by exact_mod_cast hn₀
  have hnr : (0 : ℝ) < c.hi.n := by exact_mod_cast hn₁
  have hxpos : 0 ≤ x := by linarith
  have hLU : x * time c.lo ≤ x * time c.hi := mul_le_mul_of_nonneg_left hw.2.1 hxpos
  -- lower lap bound: `(lo * n / d - 1) / 8 ≤ k`, from the low end of the cell
  have hlow : (lo * c.lo.n / c.lo.d - 1) / 8 ≤ k := by
    have hF : ((lo * c.lo.n / c.lo.d : ℕ) : ℝ) ≤ ((lo * c.lo.n : ℕ) : ℝ) / c.lo.d := Nat.cast_div_le
    have hlx : ((lo * c.lo.n : ℕ) : ℝ) / c.lo.d ≤ x * time c.lo := by
      push_cast
      unfold time Ratio.val
      rw [show x * ((scale : ℝ) * ((c.lo.n : ℝ) / c.lo.d)) = ((scale : ℝ) * x) * c.lo.n / c.lo.d by ring]
      gcongr
    have hlt : ((lo * c.lo.n / c.lo.d : ℕ) : ℝ) < 8 * (k : ℝ) + 1 := by
      rw [hkR]; linarith
    have : lo * c.lo.n / c.lo.d < 8 * k + 1 := by exact_mod_cast hlt
    omega
  -- upper lap bound: `k ≤ (maxTop * n / d + 1) / 8`, from the high end of the cell
  have hhigh : k ≤ (maxTop * c.hi.n / c.hi.d + 1) / 8 := by
    have hG : maxTop * c.hi.n < (maxTop * c.hi.n / c.hi.d + 1) * c.hi.d := by
      have := Nat.lt_div_mul_add (a := maxTop * c.hi.n) hd₁
      rw [Nat.add_mul, one_mul]; exact this
    have hGR : ((maxTop * c.hi.n : ℕ) : ℝ) / c.hi.d < ((maxTop * c.hi.n / c.hi.d : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hdr]
      exact_mod_cast hG
    have hux : x * time c.hi ≤ ((maxTop * c.hi.n : ℕ) : ℝ) / c.hi.d := by
      push_cast
      unfold time Ratio.val
      rw [show x * ((scale : ℝ) * ((c.hi.n : ℝ) / c.hi.d)) = ((scale : ℝ) * x) * c.hi.n / c.hi.d by ring]
      gcongr
    have hlt : 8 * (k : ℝ) < ((maxTop * c.hi.n / c.hi.d : ℕ) : ℝ) + 2 := by
      rw [hkR]; linarith
    have : 8 * k < maxTop * c.hi.n / c.hi.d + 2 := by exact_mod_cast hlt
    omega
  have obsLo : (obstruction c k).lo.val < scale*x := by
    unfold obstruction Ratio.val
    dsimp only
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ 8*k)]
    push_cast
    rw [hkR]
    apply (div_lt_iff₀ hnl).2
    apply (lt_div_iff₀ hdl).1
    calc
      _ < x * time c.lo := ha
      _ = ((scale : ℝ)*x*(c.lo.n : ℝ))/c.lo.d := by unfold time Ratio.val; ring
  have obsHi : scale*x < (obstruction c k).hi.val := by
    unfold obstruction Ratio.val
    dsimp only
    push_cast
    rw [hkR]
    apply (lt_div_iff₀ hnr).2
    apply (div_lt_iff₀ hdr).1
    calc
      ((scale : ℝ)*x*(c.hi.n : ℝ))/c.hi.d = x * time c.hi := by
        unfold time Ratio.val
        ring
      _ < _ := hb
  refine ⟨obstruction c k, ?_, hn₀, hn₁, obsLo, obsHi⟩
  unfold blockers
  apply List.mem_filter.2
  refine ⟨List.mem_map.2 ⟨k, List.mem_range'_1.2 ⟨by omega, by omega⟩, rfl⟩, ?_⟩
  have hmax' : scale*x ≤ (whole maxTop).val := by simpa [whole, Ratio.val] using hmax
  have hlo' : (whole lo).val ≤ scale*x := by simpa [whole, Ratio.val] using hlo
  simp only [inTopBand, Bool.and_eq_true]
  exact ⟨⟨Ratio.lt_true hn₀ hn₁ (obsLo.trans obsHi),
    Ratio.lt_true hn₀ (by decide) (obsLo.trans_le hmax')⟩,
    Ratio.lt_true (by change 0 < 1; decide) hn₁ (hlo'.trans_lt obsHi)⟩

#print axioms blockers_mem

/-- **A passing leaf gives the cell pair** [L]: `TailStrip49Cover.pair_sound` (private there) for `pairCheckN`. -/
theorem pairN_sound {box : Box} {c d : Cell} {g : Fin 7 → ℝ}
    (check : pairCheckN box c d = true) (hbox : inBox box g) (pin : g 0 = 1) :
    CellPairFor g := by
  simp only [pairCheckN, Bool.and_eq_true] at check
  obtain ⟨⟨hc, hd⟩, hsep⟩ := check
  obtain ⟨hwc, hsc⟩ := slow_sound hc hbox pin
  obtain ⟨hwd, hsd⟩ := slow_sound hd hbox pin
  refine ⟨time c.lo, time c.hi, time d.lo, time d.hi, hwc, hwd, hsc, hsd, ?_⟩
  intro x hx₀ ordered hx₁
  have hmin : (minTop : ℝ) ≤ scale*x := by norm_num [minTop,scale]; linarith
  have hmax : (scale : ℝ)*x ≤ maxTop := by norm_num [maxTop,scale]; linarith
  have hface := (hbox 4).1
  change (box.lo 4 : ℝ) ≤ scale * g 5 at hface
  have hlo : ((max minTop (box.lo 4) : Nat) : ℝ) ≤ scale*x := by
    push_cast
    exact max_le hmin (hface.trans (mul_le_mul_of_nonneg_left ordered scale_pos'.le))
  rintro ⟨b₀,b₁⟩
  have hcw : windowCheck c = true := by
    simp only [slowCheck, Bool.and_eq_true] at hc
    exact hc.1
  have hdw : windowCheck d = true := by
    simp only [slowCheck, Bool.and_eq_true] at hd
    exact hd.1
  obtain ⟨p,hp,hpl,hpu,h₀,h₁⟩ := blockers_mem hcw hlo hmin hmax b₀
  obtain ⟨q,hq,hql,hqu,h₂,h₃⟩ := blockers_mem hdw hlo hmin hmax b₁
  have h := List.all_eq_true.mp (List.all_eq_true.mp hsep p hp) q hq
  simp only [apart, Bool.or_eq_true] at h
  rcases h with h | h
  · exact (h₁.trans_le (Ratio.real_le hpu hql h)).not_ge h₂.le
  · exact (h₃.trans_le (Ratio.real_le hqu hpl h)).not_ge h₀.le

#print axioms pairN_sound

/-- **A passing certificate gives the cell pair on its box** [L]; the induction of `coverWith_sound`. -/
theorem certCheckL_sound {g : Fin 7 → ℝ} (pin : g 0 = 1) :
    ∀ (cert : CertL) (box : Box), certCheckL box cert = true → inBox box g → CellPairFor g := by
  intro cert
  induction cert with
  | leaf c d => intro box h hbox; exact pairN_sound h hbox pin
  | split l r ihl ihr =>
    intro box h hbox
    simp only [certCheckL, Bool.and_eq_true] at h
    let i := widest box
    rcases le_total ((scale : ℝ)*g (coordinate i)) (mid box i : ℝ) with ha | hb
    · apply ihl (left box i) h.1
      intro j
      by_cases hj : j = i
      · subst j
        simpa [left] using And.intro (hbox i).1 ha
      · simpa [left, hj] using hbox j
    · apply ihr (right box i) h.2
      intro j
      by_cases hj : j = i
      · subst j
        simpa [right] using And.intro hb (hbox i).2
      · simpa [right, hj] using hbox j

#print axioms certCheckL_sound

/-- Every root of the strip, as a tuple. -/
def RootOK (a b c d e : Nat) : Prop := ∃ cert : CertL, certCheckL (root a b c d e) cert = true

/-- **Certificates for every root give the conclusion of `cells_of_check`** [L; PROVISIONAL: covering], with no
`native_decide`. -/
theorem cells_of_certs
    (h : ∀ a b c d e : Nat, 1 ≤ a → a ≤ b → b ≤ c → c ≤ d → d ≤ e → e ≤ 26 → RootOK a b c d e)
    (g : Fin 7 → ℝ) (pin : g 0 = 1) (ordered : Monotone g) (hmax : g 5 ≤ 51) : CellPairFor g := by
  obtain ⟨a,b,c,d,e,ha,hab,hbc,hcd,hde,he,hbox⟩ := roots_cover pin ordered hmax
  obtain ⟨cert, hc⟩ := h a b c d e ha hab hbc hcd hde he
  exact certCheckL_sound pin cert _ hc hbox

#print axioms cells_of_certs

/-! ## Chunks: checking the certificates in separate kernel declarations -/

/-- A run of root tuples, each with its certificate. -/
def chunkOK (ts : List (Nat × Nat × Nat × Nat × Nat)) (cs : List CertL) : Bool :=
  decide (ts.length = cs.length) && (ts.zip cs).all fun p => certCheckL (rootOf p.1) p.2

theorem chunkOK_mem {ts : List (Nat × Nat × Nat × Nat × Nat)} {cs : List CertL}
    (h : chunkOK ts cs = true) {a b c d e : Nat} (hm : (a,b,c,d,e) ∈ ts) : RootOK a b c d e := by
  simp only [chunkOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  obtain ⟨i, hi, hti⟩ := List.getElem_of_mem hm
  have hi' : i < cs.length := hlen ▸ hi
  have hiz : i < (ts.zip cs).length := by rw [List.length_zip]; omega
  have hz : (ts.zip cs)[i] ∈ ts.zip cs := List.getElem_mem hiz
  have hc := hall _ hz
  rw [List.getElem_zip] at hc
  refine ⟨cs[i], ?_⟩
  have e1 : rootOf ts[i] = root a b c d e := by rw [hti]; rfl
  rw [← e1]
  exact hc

/-- Two chunks that split a list at `n` combine. -/
theorem chunkOK_split {ts : List (Nat × Nat × Nat × Nat × Nat)} {n : Nat} {c₁ c₂ : List CertL}
    (h₁ : chunkOK (ts.take n) c₁ = true) (h₂ : chunkOK (ts.drop n) c₂ = true) :
    ∀ {a b c d e : Nat}, (a,b,c,d,e) ∈ ts → RootOK a b c d e := by
  intro a b c d e hm
  rw [← List.take_append_drop n ts, List.mem_append] at hm
  rcases hm with hm | hm
  · exact chunkOK_mem h₁ hm
  · exact chunkOK_mem h₂ hm

/-- Membership in a slice. -/
theorem mem_rootTuples {a b c d e : Nat} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hde : d ≤ e)
    (he : e ≤ 26) : (a,b,c,d,e) ∈ rootTuples a := by
  simp only [rootTuples, List.mem_flatMap, List.mem_map, List.mem_range'_1]
  exact ⟨b, ⟨hab, by omega⟩, c, ⟨hbc, by omega⟩, d, ⟨hcd, by omega⟩, e, ⟨hde, by omega⟩, rfl⟩

/-- **Slices assemble** [L]: if every root tuple of every slice `1..26` has a checking certificate, the
hypothesis of `cells_of_certs` holds. -/
theorem allRoots_of_slices
    (hs : ∀ a, 1 ≤ a → a ≤ 26 → ∀ {b c d e : Nat}, (a,b,c,d,e) ∈ rootTuples a → RootOK a b c d e) :
    ∀ a b c d e : Nat, 1 ≤ a → a ≤ b → b ≤ c → c ≤ d → d ≤ e → e ≤ 26 → RootOK a b c d e :=
  fun a b c d e ha hab hbc hcd hde he =>
    hs a ha (by omega) (mem_rootTuples hab hbc hcd hde he)

#print axioms chunkOK_split
#print axioms allRoots_of_slices

/-! ## Coded certificates (E929): box-level soundness and slice assembly -/

/-- Every normalised tuple in the box has the cell pair. -/
def BoxOK (box : Box) : Prop := ∀ g : Fin 7 → ℝ, inBox box g → g 0 = 1 → CellPairFor g

/-- **Halving** [L]: the two halves of `coverWith` cover the box. -/
theorem boxOK_split {box : Box} (hl : BoxOK (left box (widest box))) (hr : BoxOK (right box (widest box))) :
    BoxOK box := by
  intro g hbox pin
  let i := widest box
  have hl' : BoxOK (left box i) := hl
  have hr' : BoxOK (right box i) := hr
  rcases le_total ((scale : ℝ)*g (coordinate i)) (mid box i : ℝ) with ha | hb
  · apply hl' g _ pin
    intro j
    by_cases hj : j = i
    · subst j
      simpa [left] using And.intro (hbox i).1 ha
    · simpa [left, hj] using hbox j
  · apply hr' g _ pin
    intro j
    by_cases hj : j = i
    · subst j
      simpa [right] using And.intro hb (hbox i).2
    · simpa [right, hj] using hbox j

#print axioms boxOK_split

/-- **A passing code gives the cell pair on its box** [L]. -/
theorem checkCode_sound : ∀ (d : Nat) (box : Box) (code : Nat), checkCode d box code = true → BoxOK box := by
  intro d
  induction d with
  | zero => intro box code h; simp [checkCode] at h
  | succ d ih =>
    intro box code h
    unfold checkCode at h
    split at h
    · intro g hbox pin; exact pairN_sound h hbox pin
    · simp only [Bool.and_eq_true] at h
      exact boxOK_split (ih _ _ h.1) (ih _ _ h.2)

#print axioms checkCode_sound

theorem boxAt_append (b : Box) (p : List Bool) (x : Bool) :
    boxAt b (p ++ [x]) = if x then right (boxAt b p) (widest (boxAt b p)) else left (boxAt b p) (widest (boxAt b p)) := by
  simp [boxAt, List.foldl_append]

/-- **Halving along a path** [L]. -/
theorem boxAt_split {b : Box} {p : List Bool} (hl : BoxOK (boxAt b (p ++ [false])))
    (hr : BoxOK (boxAt b (p ++ [true]))) : BoxOK (boxAt b p) := by
  rw [boxAt_append] at hl hr
  exact boxOK_split hl hr

theorem boxAt_nil (b : Box) : boxAt b [] = b := rfl

/-- A run of roots of slice `a` from index `s`, `n` long, all with the cell pair. -/
def Seg (a s n : Nat) : Prop := ∀ t ∈ ((rootTuples a).drop s).take n, BoxOK (rootOf t)

theorem seg_of_codeChunk {a s : Nat} {codes : List Nat} (h : codeChunkOK a s codes = true) :
    Seg a s codes.length := by
  intro t ht
  simp only [codeChunkOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  obtain ⟨i, hi, hti⟩ := List.getElem_of_mem ht
  have hi' : i < codes.length := hlen ▸ hi
  have hiz : i < ((((rootTuples a).drop s).take codes.length).zip codes).length := by
    rw [List.length_zip]; omega
  have hc := hall _ (List.getElem_mem hiz)
  rw [List.getElem_zip] at hc
  rw [← hti]
  exact checkCode_sound _ _ _ hc

theorem seg_one {a s : Nat} {t : Nat × Nat × Nat × Nat × Nat}
    (ht : ((rootTuples a).drop s).take 1 = [t]) (h : BoxOK (rootOf t)) : Seg a s 1 := by
  intro u hu
  rw [ht, List.mem_singleton] at hu
  exact hu ▸ h

theorem seg_join {a s n s' m : Nat} (h₁ : Seg a s n) (h₂ : Seg a s' m) (e : s' = s + n) :
    Seg a s (n + m) := by
  intro t ht
  subst e
  rw [List.take_add, List.mem_append, List.drop_drop] at ht
  rcases ht with ht | ht
  · exact h₁ t ht
  · have h' : t ∈ ((rootTuples a).drop (s + n)).take m := by
      simpa only [Nat.add_comm] using ht
    exact h₂ t h'

theorem slice_of_seg {a n : Nat} (h : Seg a 0 n) (hn : (rootTuples a).length ≤ n) :
    ∀ t ∈ rootTuples a, BoxOK (rootOf t) := by
  intro t ht
  apply h t
  rw [List.drop_zero, List.take_of_length_le hn]
  exact ht

/-- **The strip from slices** [L; PROVISIONAL: covering, supporting the strip's clear point]: if every root of
every slice `1..26` has the cell pair, every normalised tuple with `g 5 ≤ 51` has it. -/
theorem cells_of_slices (hs : ∀ a, 1 ≤ a → a ≤ 26 → ∀ t ∈ rootTuples a, BoxOK (rootOf t))
    (g : Fin 7 → ℝ) (pin : g 0 = 1) (ordered : Monotone g) (hmax : g 5 ≤ 51) : CellPairFor g := by
  obtain ⟨a,b,c,d,e,ha,hab,hbc,hcd,hde,he,hbox⟩ := roots_cover pin ordered hmax
  exact hs a ha (by omega) (a,b,c,d,e) (mem_rootTuples hab hbc hcd hde he) g hbox pin

#print axioms seg_join
#print axioms slice_of_seg
#print axioms cells_of_slices

end Fresh.TailStrip49Cert
