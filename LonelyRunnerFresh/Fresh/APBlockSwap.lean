import Fresh.SplitAPArrangementAll

/-! Rules1–4,8–18. Exact physical relabeling swaps the two AP blocks.
It transports negative relative offsets to positive offsets without changing
any physical speed. The finite labels are checked; c and A remain symbolic. -/
open Classical
namespace Fresh.SplitAPArrangement
open Fresh

noncomputable def blockSwap (p : ℕ) (hp2 : 2 ≤ p) (hp6 : p ≤ 6) : Equiv.Perm (Fin 8) :=
  Equiv.ofBijective
    (fun i => Fin.ofNat 8 (if (i : ℕ)<8-p then p+(i : ℕ) else (i : ℕ)-(8-p)))
    (by interval_cases p <;> decide)

theorem blockSwap_speed (c A : ℝ) (p : ℕ) (hp2 : 2 ≤ p) (hp6 : p ≤ 6) :
    speeds c A p ∘ blockSwap p hp2 hp6 = speeds (c+A) (-A) (8-p) := by
  funext i
  interval_cases p
  · fin_cases i
    · change speeds c A 2 (2 : Fin 8) = speeds (c+A) (-A) 6 (0 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 2 (3 : Fin 8) = speeds (c+A) (-A) 6 (1 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 2 (4 : Fin 8) = speeds (c+A) (-A) 6 (2 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 2 (5 : Fin 8) = speeds (c+A) (-A) 6 (3 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 2 (6 : Fin 8) = speeds (c+A) (-A) 6 (4 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 2 (7 : Fin 8) = speeds (c+A) (-A) 6 (5 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 2 (0 : Fin 8) = speeds (c+A) (-A) 6 (6 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 2 (1 : Fin 8) = speeds (c+A) (-A) 6 (7 : Fin 8)
      norm_num [speeds] <;> ring
  · fin_cases i
    · change speeds c A 3 (3 : Fin 8) = speeds (c+A) (-A) 5 (0 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 3 (4 : Fin 8) = speeds (c+A) (-A) 5 (1 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 3 (5 : Fin 8) = speeds (c+A) (-A) 5 (2 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 3 (6 : Fin 8) = speeds (c+A) (-A) 5 (3 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 3 (7 : Fin 8) = speeds (c+A) (-A) 5 (4 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 3 (0 : Fin 8) = speeds (c+A) (-A) 5 (5 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 3 (1 : Fin 8) = speeds (c+A) (-A) 5 (6 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 3 (2 : Fin 8) = speeds (c+A) (-A) 5 (7 : Fin 8)
      norm_num [speeds] <;> ring
  · fin_cases i
    · change speeds c A 4 (4 : Fin 8) = speeds (c+A) (-A) 4 (0 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 4 (5 : Fin 8) = speeds (c+A) (-A) 4 (1 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 4 (6 : Fin 8) = speeds (c+A) (-A) 4 (2 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 4 (7 : Fin 8) = speeds (c+A) (-A) 4 (3 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 4 (0 : Fin 8) = speeds (c+A) (-A) 4 (4 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 4 (1 : Fin 8) = speeds (c+A) (-A) 4 (5 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 4 (2 : Fin 8) = speeds (c+A) (-A) 4 (6 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 4 (3 : Fin 8) = speeds (c+A) (-A) 4 (7 : Fin 8)
      norm_num [speeds] <;> ring
  · fin_cases i
    · change speeds c A 5 (5 : Fin 8) = speeds (c+A) (-A) 3 (0 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 5 (6 : Fin 8) = speeds (c+A) (-A) 3 (1 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 5 (7 : Fin 8) = speeds (c+A) (-A) 3 (2 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 5 (0 : Fin 8) = speeds (c+A) (-A) 3 (3 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 5 (1 : Fin 8) = speeds (c+A) (-A) 3 (4 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 5 (2 : Fin 8) = speeds (c+A) (-A) 3 (5 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 5 (3 : Fin 8) = speeds (c+A) (-A) 3 (6 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 5 (4 : Fin 8) = speeds (c+A) (-A) 3 (7 : Fin 8)
      norm_num [speeds] <;> ring
  · fin_cases i
    · change speeds c A 6 (6 : Fin 8) = speeds (c+A) (-A) 2 (0 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 6 (7 : Fin 8) = speeds (c+A) (-A) 2 (1 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 6 (0 : Fin 8) = speeds (c+A) (-A) 2 (2 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 6 (1 : Fin 8) = speeds (c+A) (-A) 2 (3 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 6 (2 : Fin 8) = speeds (c+A) (-A) 2 (4 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 6 (3 : Fin 8) = speeds (c+A) (-A) 2 (5 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 6 (4 : Fin 8) = speeds (c+A) (-A) 2 (6 : Fin 8)
      norm_num [speeds] <;> ring
    · change speeds c A 6 (5 : Fin 8) = speeds (c+A) (-A) 2 (7 : Fin 8)
      norm_num [speeds] <;> ring

theorem negative_two_block_all (c A : ℝ) (p : ℕ) (hp2 : 2 ≤ p) (hp6 : p ≤ 6)
    (hnegative : A+((7-p : ℕ) : ℝ)<0) : ∀ k : Fin 8, Isolation (speeds c A p) k := by
  have hq2 : 2 ≤ 8-p := by omega
  have hq6 : 8-p ≤ 6 := by omega
  have hgap : ((8-p : ℕ) : ℝ)-1 < -A := by
    have hnat : 8-p=(7-p)+1 := by omega
    rw [hnat]
    push_cast
    linarith
  have hnew := two_block_all (c+A) (-A) (8-p) hq2 hq6 hgap
  intro k
  have hh := hnew ((blockSwap p hp2 hp6).symm k)
  rw [← blockSwap_speed c A p hp2 hp6] at hh
  have ho := (Fresh.isolation_comp_perm (speeds c A p) (blockSwap p hp2 hp6) ((blockSwap p hp2 hp6).symm k)).1 hh
  simpa using ho

#print axioms blockSwap_speed
#print axioms negative_two_block_all
end Fresh.SplitAPArrangement
