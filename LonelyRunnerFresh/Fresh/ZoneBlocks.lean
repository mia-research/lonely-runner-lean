import Fresh.M4ZoneAssembly
import Fresh.ZoneDecode

/-!
# Zone chunks assembled from kernel-checked blocks (2026-11-22)

New file; nothing existing is edited.

One `decide +kernel` over a whole chunk keeps every intermediate zone matrix in the kernel's
cache: the chunk `(4,5,6)` (364 tuples, 36,770 certificate nodes) reached 28 GB.  A chunk is
therefore split into blocks `B` of `(tail, code)` pairs, each checked by its own kernel
theorem `zblk v w x B = true`, and `zchunk_of_blocks` assembles them.  The statement proved
for each chunk is unchanged: `zchunk v w x cs = true`.
-/

namespace Fresh.M4ZoneAssembly

open Fresh.ZoneCover Fresh.M4SplitAssembly

/-- A block: every tail `t` with code `d` has `zverdict (1 :: v :: w :: x :: t) (dec1 d)`. -/
def zblk (v w x : ℕ) (B : List (List ℕ × List ℕ)) : Bool :=
  B.all (fun p => zverdict (1 :: v :: w :: x :: p.1) (ZT.dec1 p.2))

theorem zblk_append (v w x : ℕ) (A B : List (List ℕ × List ℕ)) :
    zblk v w x (A ++ B) = (zblk v w x A && zblk v w x B) := by
  simp [zblk, List.all_append]

theorem zchunk_of_blocks (v w x : ℕ) (L : List (List ℕ × List ℕ))
    (hg : gen 3 x = L.map Prod.fst) (hb : zblk v w x L = true) :
    zchunk v w x (L.map (fun p => ZT.dec1 p.2)) = true := by
  unfold zchunk
  rw [hg]
  have hz : ∀ M : List (List ℕ × List ℕ),
      List.zip (M.map Prod.fst) (M.map (fun p => ZT.dec1 p.2)) =
        M.map (fun p => (p.1, ZT.dec1 p.2)) := by
    intro M
    induction M with
    | nil => rfl
    | cons a M ih => simp [ih]
  rw [hz]
  simp only [List.length_map, decide_true, Bool.true_and, List.all_map]
  exact hb

#print axioms zchunk_of_blocks

end Fresh.M4ZoneAssembly
