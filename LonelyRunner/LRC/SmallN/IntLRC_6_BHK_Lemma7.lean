import LonelyRunner.LRC.SmallN.IntLRC_6_BHK_MainLemma

/-!
# BHK Lemma 7 — the order bound for a minimal group element

BHK strengthen the notion of "minimal element" used in the Main Lemma and
Corollary 6.  For `i, j ≥ 0` let

  `Z_{i,j} = [-i, i] × [-j, j] \ {(±i, ±j)}`

and call `(i/n, j/n) ∈ G` *minimal* (BHK (13)) when
`{(k/n, l/n) : (k, l) ∈ Z_{|i|,|j|} ∩ G} = {(0, 0)}`.  Lemma 7 is the lower
bound on the order `n = |G|` of a group having such a minimal element:

  `|i|, |j| ≥ 1 ⇒ n ≥ (|i| + 1)(|j| + 1) − 2`  (BHK (14), main part).

**Proof (BHK).**  Put `Y = [0, i] × [0, j] \ {(i, 0), (i, j)}`, so that
`Y − Y ⊆ Z_{i,j}` (removing the two points `(i,0)`, `(i,j)` is exactly what
prevents a difference of two `Y`-points from landing on a corner `(±i, ±j)`).
Minimality then makes the translates `{g + Y : g ∈ G}` pairwise disjoint, so the
map `G × Y → (ℤ/n)²`, `(g, y) ↦ g + y`, is injective.  Hence
`|G| · |Y| ≤ n²`, and with `|G| = n`, `|Y| = (i+1)(j+1) − 2` this gives (14).

This is the combinatorial prerequisite for the §5 (Proposition 11) exceptional
-pair reductions: combined with the "full vertical length `1/6 ⟹ q < 6|j|`"
upper bound it eliminates the high-`|j|` and `gcd(i,q) > 1` anti-diagonal pairs
that the pure-congruence kills (`bhk_prop11_exc_anti_diag`, gcd 1 only) cannot
reach.

## Source

T. Bohman, R. Holzman, D. Kleitman, *Six Lonely Runners*, EJC **8** (2001) R3,
§3.3 (Lemma 7) — pp. 11.
-/

open scoped Finset

namespace BHK

/-- **BHK Lemma 7, main part (combinatorial core over `H`).**  Let
`H ⊆ (ℤ/n)²` be a subgroup of order `n` (`n > 1`), and let `i, j ≥ 1` with
`i, j < n` (so the box `[0,i] × [0,j]` embeds injectively into `(ℤ/n)²`).
If `H` contains no nonzero point of `Z_{i,j} = [-i,i] × [-j,j] \ {(±i, ±j)}`
(the (13)-minimality hypothesis), then `n ≥ (i+1)(j+1) − 2`. -/
lemma bhk_lemma7_card (n : ℕ) (hn : 1 < n)
    (H : AddSubgroup (ZMod n × ZMod n)) (hH : Nat.card H = n)
    (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hin : i < n) (hjn : j < n)
    (hmin : ∀ k l : ℤ, (k, l) ≠ (0, 0) → |k| ≤ (i : ℤ) → |l| ≤ (j : ℤ) →
        ¬(|k| = (i : ℤ) ∧ |l| = (j : ℤ)) →
        (((k : ZMod n), (l : ZMod n)) : ZMod n × ZMod n) ∉ H) :
    (i + 1) * (j + 1) - 2 ≤ n := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  -- The box of representatives `[0,i] × [0,j]` (as `ℕ × ℕ`) and the two
  -- corner points BHK removes.
  set box : Finset (ℕ × ℕ) := Finset.range (i + 1) ×ˢ Finset.range (j + 1) with hbox
  set corners : Finset (ℕ × ℕ) := {(i, 0), (i, j)} with hcorners
  set Y₀ : Finset (ℕ × ℕ) := box \ corners with hY₀
  -- The embedding into the torus group.
  set emb : ℕ × ℕ → ZMod n × ZMod n := fun ab => ((ab.1 : ZMod n), (ab.2 : ZMod n)) with hemb
  set Y : Finset (ZMod n × ZMod n) := Y₀.image emb with hYdef
  set S : Finset (ZMod n × ZMod n) := Finset.univ.filter (· ∈ H) with hSdef
  -- `emb` is injective on the box (coords `< n`).
  have hcast_inj : ∀ a b : ℕ, a < n → b < n → (a : ZMod n) = (b : ZMod n) → a = b := by
    intro a b ha hb hab
    have := congrArg ZMod.val hab
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  have hemb_injOn : Set.InjOn emb box := by
    intro x hx y hy hxy
    rw [Finset.coe_product, Set.mem_prod] at hx hy
    simp only [Finset.coe_range, Set.mem_Iio] at hx hy
    obtain ⟨hx1, hx2⟩ := hx; obtain ⟨hy1, hy2⟩ := hy
    have h1 : x.1 = y.1 := hcast_inj _ _ (by omega) (by omega) (congrArg Prod.fst hxy)
    have h2 : x.2 = y.2 := hcast_inj _ _ (by omega) (by omega) (congrArg Prod.snd hxy)
    exact Prod.ext h1 h2
  -- `|Y| = (i+1)(j+1) - 2`.
  have hbox_card : box.card = (i + 1) * (j + 1) := by
    rw [hbox, Finset.card_product, Finset.card_range, Finset.card_range]
  have hcorners_sub : corners ⊆ box := by
    rw [hcorners, Finset.insert_subset_iff, Finset.singleton_subset_iff, hbox]
    exact ⟨Finset.mk_mem_product (Finset.mem_range.mpr (by omega)) (Finset.mem_range.mpr (by omega)),
           Finset.mk_mem_product (Finset.mem_range.mpr (by omega)) (Finset.mem_range.mpr (by omega))⟩
  have hcorners_card : corners.card = 2 := by
    rw [hcorners]
    exact Finset.card_pair (by intro hcon; rw [Prod.mk.injEq] at hcon; omega)
  have hY₀_card : Y₀.card = (i + 1) * (j + 1) - 2 := by
    have hcard := Finset.card_sdiff_add_card_eq_card hcorners_sub
    rw [← hY₀, hbox_card, hcorners_card] at hcard
    omega
  have hY_card : Y.card = (i + 1) * (j + 1) - 2 := by
    rw [hYdef, Finset.card_image_of_injOn (hemb_injOn.mono (by rw [hY₀]; exact Finset.sdiff_subset)),
      hY₀_card]
  -- `|S| = n`.
  have hS_card : S.card = n := by
    rw [hSdef, ← Fintype.card_subtype (· ∈ H), ← Nat.card_eq_fintype_card]
    exact hH
  -- The map `(g, y) ↦ g + y` is injective on `S ×ˢ Y`.
  have hmap_inj : Set.InjOn (fun p : (ZMod n × ZMod n) × (ZMod n × ZMod n) => p.1 + p.2)
      (↑(S ×ˢ Y) : Set ((ZMod n × ZMod n) × (ZMod n × ZMod n))) := by
    intro p hp p' hp' heq
    rw [Finset.mem_coe, Finset.mem_product] at hp hp'
    obtain ⟨hpS, hpY⟩ := hp
    obtain ⟨hp'S, hp'Y⟩ := hp'
    rw [hSdef, Finset.mem_filter] at hpS hp'S
    obtain ⟨-, hpH⟩ := hpS
    obtain ⟨-, hp'H⟩ := hp'S
    rw [hYdef, Finset.mem_image] at hpY hp'Y
    obtain ⟨⟨a₁, b₁⟩, hab₁, hemb₁⟩ := hpY
    obtain ⟨⟨a₂, b₂⟩, hab₂, hemb₂⟩ := hp'Y
    simp only [hemb] at hemb₁ hemb₂
    -- box bounds and corner exclusions for both representatives
    rw [hY₀, Finset.mem_sdiff] at hab₁ hab₂
    obtain ⟨hin₁, hcor₁⟩ := hab₁
    obtain ⟨hin₂, hcor₂⟩ := hab₂
    rw [hbox, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hin₁ hin₂
    obtain ⟨ha₁, hb₁⟩ := hin₁
    obtain ⟨ha₂, hb₂⟩ := hin₂
    rw [hcorners, Finset.mem_insert, Finset.mem_singleton, not_or] at hcor₁ hcor₂
    -- `heq` as an equation of group elements
    have h : p.1 + p.2 = p'.1 + p'.2 := heq
    -- `p'.2 - p.2 ∈ H`
    have hdiff_mem : p'.2 - p.2 ∈ H := by
      have hsub : p'.2 - p.2 = p.1 - p'.1 := by linear_combination -h
      rw [hsub]; exact H.sub_mem hpH hp'H
    -- identify the difference with the integer pair `(a₂-a₁, b₂-b₁)` reduced mod n
    set k : ℤ := (a₂ : ℤ) - (a₁ : ℤ) with hk
    set l : ℤ := (b₂ : ℤ) - (b₁ : ℤ) with hl
    have hmem_kl : (((k : ZMod n), (l : ZMod n)) : ZMod n × ZMod n) ∈ H := by
      have heqkl : (((k : ZMod n), (l : ZMod n)) : ZMod n × ZMod n) = p'.2 - p.2 := by
        rw [← hemb₂, ← hemb₁, hk, hl, Prod.mk_sub_mk, Prod.mk.injEq]
        constructor <;> push_cast <;> ring
      rw [heqkl]; exact hdiff_mem
    have hk_abs : |k| ≤ (i : ℤ) := by rw [hk, abs_le]; omega
    have hl_abs : |l| ≤ (j : ℤ) := by rw [hl, abs_le]; omega
    by_cases hkl0 : (k, l) = (0, 0)
    · -- zero difference: the box reps coincide, hence both coordinates do
      have hk0 : k = 0 := congrArg Prod.fst hkl0
      have hl0 : l = 0 := congrArg Prod.snd hkl0
      have ha : a₁ = a₂ := by rw [hk] at hk0; omega
      have hb : b₁ = b₂ := by rw [hl] at hl0; omega
      have hp2eq : p.2 = p'.2 := by rw [← hemb₁, ← hemb₂, ha, hb]
      have hp1eq : p.1 = p'.1 := by rw [hp2eq] at h; exact add_right_cancel h
      exact Prod.ext hp1eq hp2eq
    · exfalso
      by_cases hcorner : |k| = (i : ℤ) ∧ |l| = (j : ℤ)
      · -- corner difference: one of the box reps is a removed corner
        obtain ⟨hki, hlj⟩ := hcorner
        rw [hk, abs_eq (by positivity)] at hki
        rw [hl, abs_eq (by positivity)] at hlj
        rcases hki with hki | hki <;> rcases hlj with hlj | hlj
        · -- a₂=i,a₁=0,b₂=j,b₁=0 : (a₂,b₂)=(i,j)
          exact hcor₂.2 (Prod.ext (by omega) (by omega))
        · -- a₂=i,a₁=0,b₂=0,b₁=j : (a₂,b₂)=(i,0)
          exact hcor₂.1 (Prod.ext (by omega) (by omega))
        · -- a₂=0,a₁=i,b₂=j,b₁=0 : (a₁,b₁)=(i,0)
          exact hcor₁.1 (Prod.ext (by omega) (by omega))
        · -- a₂=0,a₁=i,b₂=0,b₁=j : (a₁,b₁)=(i,j)
          exact hcor₁.2 (Prod.ext (by omega) (by omega))
      · exact hmin k l hkl0 hk_abs hl_abs hcorner hmem_kl
  -- counting: `|S| · |Y| ≤ n²`
  have hcard_le : (S ×ˢ Y).card ≤ (Finset.univ : Finset (ZMod n × ZMod n)).card :=
    Finset.card_le_card_of_injOn (fun p => p.1 + p.2) (fun _ _ => Finset.mem_univ _) hmap_inj
  have huniv : (Finset.univ : Finset (ZMod n × ZMod n)).card = n * n := by
    simp only [Finset.card_univ, Fintype.card_prod, ZMod.card]
  rw [Finset.card_product, hS_card, hY_card, huniv] at hcard_le
  -- cancel the factor `n`
  exact Nat.le_of_mul_le_mul_left hcard_le (by omega)

/-- **BHK Lemma 7, main part (group form).**  Phrased over `IsBHKLift G n` and the
(13)-minimality predicate exactly as produced by `bhk_s7_corollary_6_minimal`
(`((k/n, l/n) ∉ G)` for the off-corner box points).  For a minimal nonzero pair
`(i, j)` with `i, j ≠ 0` and `|i|, |j| < n`, the order satisfies
`n ≥ (|i| + 1)(|j| + 1) − 2` (BHK (14), main part). -/
lemma bhk_lemma7 (G : Set (ℝ × ℝ)) (n : ℕ) (hn : 1 < n) (hG_lift : IsBHKLift G n)
    (i j : ℤ) (hi : i ≠ 0) (hj : j ≠ 0)
    (hin : i.natAbs < n) (hjn : j.natAbs < n)
    (hmin : ∀ kl : ℤ × ℤ, kl ≠ (0, 0) → |kl.1| ≤ |i| → |kl.2| ≤ |j| →
        ¬(|kl.1| = |i| ∧ |kl.2| = |j|) → ((kl.1 : ℝ) / n, (kl.2 : ℝ) / n) ∉ G) :
    (i.natAbs + 1) * (j.natAbs + 1) - 2 ≤ n := by
  obtain ⟨H, hH_card, hG_iff⟩ := hG_lift
  refine bhk_lemma7_card n hn H hH_card i.natAbs j.natAbs (by omega) (by omega) hin hjn ?_
  intro k l hkl0 hk_abs hl_abs hcorner
  rw [← bhk_lift_int_mem_iff G n hn H hG_iff k l]
  refine hmin (k, l) hkl0 ?_ ?_ ?_
  · rw [Int.abs_eq_natAbs i]; exact hk_abs
  · rw [Int.abs_eq_natAbs j]; exact hl_abs
  · rw [Int.abs_eq_natAbs i, Int.abs_eq_natAbs j]; exact hcorner

/-- **Grid pigeonhole (the `q < 6|j|` equidistribution engine).**  When `m ∣ q`
(`0 < m ≤ q`) the multiples of `m/q` form an `m/q`-spaced grid on the circle, so
every window `[y, y + m/q]` lying in `[0, 1]` contains one.  This is the kernel of
BHK's Part-4 "a segment of `L_{i,j}` meets `R` with full vertical length `1/6`,
hence `C ∩ R = ∅ ⇒ q < 6|j|`" argument (Cases 5.2.2/5.2.3): the coset's coordinates
on the segment are `|j|/q`-spaced, so avoiding the length-`1/6` crossing forces
`|j|/q > 1/6`. -/
lemma bhk_prop11_grid_hit (m q : ℕ) (hm : 0 < m) (hq : 0 < q) (hmdvd : m ∣ q)
    (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y + (m : ℝ) / q ≤ 1) :
    ∃ t : ℕ, Int.fract ((t * m : ℝ) / q) ∈ Set.Icc y (y + (m : ℝ) / q) := by
  obtain ⟨d, hd⟩ := hmdvd
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, Nat.mul_zero] at hd; omega
    · exact h
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hqmd : (q : ℝ) = (m : ℝ) * d := by exact_mod_cast hd
  have hmq_eq : (m : ℝ) / q = 1 / d := by rw [hqmd]; field_simp
  rw [hmq_eq] at hy1 ⊢
  set s : ℕ := ⌈y * d⌉₊ with hs
  -- `s ≤ d - 1`, so `s < d` and the grid point `s/d` lies in `[0, 1)`.
  have hyd_le : y * d ≤ (d : ℝ) - 1 := by
    have hy' : y ≤ 1 - 1 / d := by linarith
    have h1 : y * d ≤ (1 - 1 / d) * d := mul_le_mul_of_nonneg_right hy' hdR.le
    have h2 : (1 - 1 / d) * d = (d : ℝ) - 1 := by field_simp
    linarith
  have hsd : s < d := by
    have : s ≤ d - 1 := by
      rw [hs, Nat.ceil_le, Nat.cast_sub hd0, Nat.cast_one]; exact hyd_le
    omega
  have hsmq : (s * m : ℝ) / q = (s : ℝ) / d := by rw [hqmd]; field_simp
  have hfract : Int.fract ((s * m : ℝ) / q) = (s : ℝ) / d := by
    rw [hsmq, Int.fract_eq_self.mpr ⟨by positivity, ?_⟩]
    rw [div_lt_one hdR]; exact_mod_cast hsd
  refine ⟨s, ?_⟩
  rw [hfract]
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hdR, hs]; exact Nat.le_ceil _
  · rw [div_le_iff₀ hdR]
    have hub : (s : ℝ) < y * d + 1 := by rw [hs]; exact Nat.ceil_lt_add_one (by positivity)
    have he : (y + 1 / d) * d = y * d + 1 := by field_simp
    rw [he]; linarith

/-- **`q < 6m` from a missed window (the Part-4 `q < 6|j|` bound).**  If the
`m/q`-spaced grid (`m ∣ q`) avoids a closed window `[y, y + 1/6]` inside `[0, 1]`,
then its spacing exceeds `1/6`, i.e. `q < 6m`.  This is the directly-usable form of
BHK's Case 5.2.2/5.2.3 conclusion: with `m = |j|` and the missed window the
full-height crossing of `R`, `C ∩ R = ∅` yields `q < 6|j|`.  (The remaining Part-4
obligation is to exhibit the coset's coordinates on the segment as this grid and the
crossing as the missed window.) -/
lemma bhk_prop11_grid_avoid (m q : ℕ) (hm : 0 < m) (hq : 0 < q) (hmdvd : m ∣ q)
    (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y + 1 / 6 ≤ 1)
    (havoid : ∀ t : ℕ, Int.fract ((t * m : ℝ) / q) ∉ Set.Icc y (y + 1 / 6)) :
    q < 6 * m := by
  by_contra hle
  push_neg at hle
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hmq6 : (m : ℝ) / q ≤ 1 / 6 := by
    rw [div_le_iff₀ hqR]
    have h6 : (6 : ℝ) * m ≤ q := by exact_mod_cast hle
    linarith
  have hy1' : y + (m : ℝ) / q ≤ 1 := by linarith
  obtain ⟨t, ht⟩ := bhk_prop11_grid_hit m q hm hq hmdvd y hy0 hy1'
  exact havoid t ⟨ht.1, le_trans ht.2 (by linarith)⟩

/-- **Coset grid pigeonhole.**  A `1/e`-spaced coset `{ b + t/e : t ∈ ℤ }` meets every
closed window `[y, y + w]` of length `w ≥ 1/e` lying inside `[0, 1]`.  This is the coset
form of `bhk_prop11_grid_hit` needed for the anti-diagonal Case 5.2.2: on a slope-`-1`
circle of `L_{i,-i}` the coset's second coordinates are `1/e`-spaced (`e = gcd(r+p, q)`),
so any crossing of `R` of vertical length `≥ 1/e` contains one. -/
lemma bhk_prop11_grid_hit_coset (e : ℕ) (he : 0 < e) (b y w : ℝ)
    (hw : 1 / (e : ℝ) ≤ w) (hy0 : 0 ≤ y) (hy1 : y + w ≤ 1) :
    ∃ t : ℤ, Int.fract (b + (t : ℝ) / e) ∈ Set.Icc y (y + w) := by
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  refine ⟨⌈(y - b) * (e : ℝ)⌉, ?_⟩
  have hlo : y ≤ b + ((⌈(y - b) * (e : ℝ)⌉ : ℤ) : ℝ) / e := by
    have h : y - b ≤ ((⌈(y - b) * (e : ℝ)⌉ : ℤ) : ℝ) / e :=
      (le_div_iff₀ heR).mpr (Int.le_ceil _)
    linarith
  have hhi0 : ((⌈(y - b) * (e : ℝ)⌉ : ℤ) : ℝ) / e < (y - b) + 1 / e := by
    rw [div_lt_iff₀ heR, show ((y - b) + 1 / (e : ℝ)) * e = (y - b) * e + 1 from by field_simp]
    exact Int.ceil_lt_add_one _
  have hhi : b + ((⌈(y - b) * (e : ℝ)⌉ : ℤ) : ℝ) / e < y + w := by linarith
  rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
  exact ⟨hlo, le_of_lt hhi⟩

/-- **Coprime-step coset grid pigeonhole.**  When `gcd(c, e) = 1`, the coset
`{ b + t·c/e : t ∈ ℤ }` equals the plain `1/e`-coset, so it too meets every window of
length `≥ 1/e` in `[0,1]`.  On a slope-`-1` circle of `L_{i,-i}` the second coordinate
advances by `p/e` per step (with `gcd(p,e) = 1`), so this is the form the anti-diagonal
witness search consumes. -/
lemma bhk_prop11_grid_hit_coset_step (e : ℕ) (he : 0 < e) (c : ℕ) (hc : Nat.Coprime c e)
    (b y w : ℝ) (hw : 1 / (e : ℝ) ≤ w) (hy0 : 0 ≤ y) (hy1 : y + w ≤ 1) :
    ∃ t : ℤ, Int.fract (b + (t : ℝ) * c / e) ∈ Set.Icc y (y + w) := by
  obtain ⟨t', ht'⟩ := bhk_prop11_grid_hit_coset e he b y w hw hy0 hy1
  have hcop : IsCoprime (c : ℤ) (e : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; simpa [Int.gcd] using hc
  obtain ⟨a, b', hab⟩ := hcop
  have hab' : (a : ℝ) * c + b' * e = 1 := by exact_mod_cast hab
  have he0 : (e : ℝ) ≠ 0 := by positivity
  refine ⟨t' * a, ?_⟩
  have heq : b + ((t' * a : ℤ) : ℝ) * (c : ℝ) / e
      = (b + (t' : ℝ) / e) + ((-(t' * b') : ℤ) : ℝ) := by
    push_cast; field_simp; linear_combination (t' : ℝ) * hab'
  rw [heq, Int.fract_add_intCast]
  exact ht'

/-- **Anti-diagonal divisibility.**  If `q ∣ i·m` then `q / gcd(i,q)` divides `m` and so
is `≤ gcd(m, q)`.  Applied with `m = r + p` and the exceptional relation `q ∣ i·(r+p)` of
the pair `(i, -i)`: the slope-`-1` circles of `L_{i,-i}` carry the coset on a
`1/gcd(r+p,q)`-spaced grid, and `gcd(r+p,q) ≥ q/gcd(i,q) ≥ 6` once `q ≥ 6·gcd(i,q)`. -/
lemma bhk_prop11_antidiag_arith (i q m : ℕ) (hi : 0 < i) (hq : 0 < q) (hdvd : q ∣ i * m) :
    (q / Nat.gcd i q) ∣ m ∧ q / Nat.gcd i q ≤ Nat.gcd m q := by
  have hgpos : 0 < Nat.gcd i q := Nat.gcd_pos_of_pos_left q hi
  set d := Nat.gcd i q with hd
  have hdi : d ∣ i := Nat.gcd_dvd_left i q
  have hdq : d ∣ q := Nat.gcd_dvd_right i q
  have hcop : Nat.Coprime (q / d) (i / d) := (Nat.coprime_div_gcd_div_gcd hgpos).symm
  have key : (q / d) ∣ (i / d) * m := by
    have e1 : d * (q / d) ∣ d * ((i / d) * m) := by
      rw [Nat.mul_div_cancel' hdq, ← mul_assoc, Nat.mul_div_cancel' hdi]; exact hdvd
    exact (Nat.mul_dvd_mul_iff_left hgpos).mp e1
  have hm : (q / d) ∣ m := hcop.dvd_of_dvd_mul_left key
  exact ⟨hm, Nat.le_of_dvd (Nat.gcd_pos_of_pos_right m hq)
    (Nat.dvd_gcd hm ⟨d, (Nat.div_mul_cancel hdq).symm⟩)⟩

end BHK
