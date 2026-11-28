import Fresh.BandNoCarve

/-!
# X24 pilot slice: per-leaf membership theorems for the (23,25) band residue

Data-side pilot for the X24 (23,25) residue (E983 item 3; the band with no
certificate dump).  Source: `x24_leafdump_v1.jsonl` (exact-Fraction certificates,
independently re-verified), built on the fixed-R0-resistant leaves of the verbatim
E832 DFS (`frontier_box_dfs_v1.c` run `23 26 64`: 297,765 root boxes = the audit
universe of `obligation_audit_2026_11_11/x24.out`, 27,349 resistant leaves at
D = 64; the run reproduces E832's recorded `[23,25)` D = 32 artifact bit-for-bit:
179,010 root boxes, 9,533,510 nodes, 7,200 leaves).  Classification (exact,
uniform-lap family, no subdivision needed at D = 64): 6,323 fixedR0 (exact
single-point W0 windows off the C certifier's dyadic grid -- the E833 item 4
mechanism) + 21,026 w1 (a common clear point in [9,15] with per-reading laps --
the `Fresh.BandNoCarve.BandW1` payload; the X24 carve region lives here).  No
resistant leaves, no START/END boundary artifacts (the resistant slab rho6 in
[6.52, 7.02] touches neither 22.5 nor 25.5).

Carve cross-check: all 90 in-band recorded carves (E828/E829 loader; 6 of the 96
sit in the lap-2 strip rho7 in (15,17), outside X24) are exact carves of [1,7]
with a W1-clear component below 17, and each lies in EXACTLY ONE w1 leaf (78
carve-containing leaves; 0 carves in any W0-certified leaf).

This file: a ~20-leaf pilot, type-balanced over the shapes present (all dump
leaves are D = 64 with equal volume, so smallest-volume selection degenerates;
within each shape the smallest cell tuple leads; carve-containing w1 leaves lead
the w1 shape), each as a per-leaf membership theorem.  Index mapping (E832/E845
convention): Lean
index 0 = rho1 = 1 (`loLxx 0 = hiLxx 0 = 1`), artifact index i = Lean index i+1.
The certificate inequalities are all closed rational comparisons, proved by
`norm_num`; the full landing is per-leaf theorems of exactly this shape, one per
JSONL line (27,349 leaves; the pilot is the worked pattern).
-/

namespace Fresh.X24Pilot

open Fresh.Certs

/-- The W1 step, index-uniform: box faces + per-reading laps give `BandW1`.
Index 0 is carried by the faces themselves (`L 0 = H 0 = 1`, so `hbox 0` pins
`g 0 = 1` and `S` lies in rho1's own gap `[9,15]`). -/
theorem w1_of_faces {g : Fin 7 → ℝ} {S : ℝ} {L H : Fin 7 → ℝ} {J : Fin 7 → ℤ}
    (hS9 : 9 ≤ S) (hS15 : S ≤ 15)
    (hcert : ∀ i, (((8 * J i : ℤ) : ℝ) + 1) ≤ L i * S ∧ H i * S ≤ (((8 * J i : ℤ) : ℝ) + 7))
    (hbox : ∀ i, L i ≤ g i ∧ g i ≤ H i) :
    Fresh.BandNoCarve.BandW1 g := by
  refine ⟨S, hS9, hS15, fun i => ?_⟩
  obtain ⟨h1, h2⟩ := hcert i
  obtain ⟨k1, k2⟩ := hbox i
  have hS0 : (0 : ℝ) ≤ S := by linarith
  refine ⟨J i, Set.mem_Icc.mpr ⟨?_, ?_⟩⟩
  · exact le_trans h1 (mul_le_mul_of_nonneg_right k1 hS0)
  · exact le_trans (mul_le_mul_of_nonneg_right k2 hS0) h2

#print axioms w1_of_faces

/-- JSONL leaf D=64 n=[171, 231, 297, 381, 423, 1472], type w1, carves [12] (of 90 in-band) -/
noncomputable def lox24_leaf_01 : Fin 7 → ℝ := ![1, (171:ℝ)/64, (231:ℝ)/64, (297:ℝ)/64, (381:ℝ)/64, (423:ℝ)/64, (1472:ℝ)/64]
noncomputable def hix24_leaf_01 : Fin 7 → ℝ := ![1, (172:ℝ)/64, (232:ℝ)/64, (298:ℝ)/64, (382:ℝ)/64, (424:ℝ)/64, (1473:ℝ)/64]
def jx24_leaf_01 : Fin 7 → ℤ := ![1, 3, 4, 5, 7, 8, 28]
theorem x24_leaf_01 (g : Fin 7 → ℝ)
    (hbox : ∀ i : Fin 7, lox24_leaf_01 i ≤ g i ∧ g i ≤ hix24_leaf_01 i) :
    Fresh.BandNoCarve.BandW1 g :=
  w1_of_faces (S := (4160:ℝ)/423) (J := jx24_leaf_01) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> simp [lox24_leaf_01, hix24_leaf_01, jx24_leaf_01] <;> norm_num)
    hbox

#print axioms x24_leaf_01

/-- JSONL leaf D=64 n=[171, 232, 297, 382, 423, 1476], type w1, carves [82] (of 90 in-band) -/
noncomputable def lox24_leaf_02 : Fin 7 → ℝ := ![1, (171:ℝ)/64, (232:ℝ)/64, (297:ℝ)/64, (382:ℝ)/64, (423:ℝ)/64, (1476:ℝ)/64]
noncomputable def hix24_leaf_02 : Fin 7 → ℝ := ![1, (172:ℝ)/64, (233:ℝ)/64, (298:ℝ)/64, (383:ℝ)/64, (424:ℝ)/64, (1477:ℝ)/64]
def jx24_leaf_02 : Fin 7 → ℤ := ![1, 3, 4, 5, 7, 8, 28]
theorem x24_leaf_02 (g : Fin 7 → ℝ)
    (hbox : ∀ i : Fin 7, lox24_leaf_02 i ≤ g i ∧ g i ≤ hix24_leaf_02 i) :
    Fresh.BandNoCarve.BandW1 g :=
  w1_of_faces (S := (4160:ℝ)/423) (J := jx24_leaf_02) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> simp [lox24_leaf_02, hix24_leaf_02, jx24_leaf_02] <;> norm_num)
    hbox

#print axioms x24_leaf_02

/-- JSONL leaf D=64 n=[171, 232, 298, 382, 423, 1474], type w1, carves [32] (of 90 in-band) -/
noncomputable def lox24_leaf_03 : Fin 7 → ℝ := ![1, (171:ℝ)/64, (232:ℝ)/64, (298:ℝ)/64, (382:ℝ)/64, (423:ℝ)/64, (1474:ℝ)/64]
noncomputable def hix24_leaf_03 : Fin 7 → ℝ := ![1, (172:ℝ)/64, (233:ℝ)/64, (299:ℝ)/64, (383:ℝ)/64, (424:ℝ)/64, (1475:ℝ)/64]
def jx24_leaf_03 : Fin 7 → ℤ := ![1, 3, 4, 5, 7, 8, 28]
theorem x24_leaf_03 (g : Fin 7 → ℝ)
    (hbox : ∀ i : Fin 7, lox24_leaf_03 i ≤ g i ∧ g i ≤ hix24_leaf_03 i) :
    Fresh.BandNoCarve.BandW1 g :=
  w1_of_faces (S := (4160:ℝ)/423) (J := jx24_leaf_03) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> simp [lox24_leaf_03, hix24_leaf_03, jx24_leaf_03] <;> norm_num)
    hbox

#print axioms x24_leaf_03

/-- JSONL leaf D=64 n=[171, 232, 298, 382, 424, 1477], type w1, carves [6] (of 90 in-band) -/
noncomputable def lox24_leaf_04 : Fin 7 → ℝ := ![1, (171:ℝ)/64, (232:ℝ)/64, (298:ℝ)/64, (382:ℝ)/64, (424:ℝ)/64, (1477:ℝ)/64]
noncomputable def hix24_leaf_04 : Fin 7 → ℝ := ![1, (172:ℝ)/64, (233:ℝ)/64, (299:ℝ)/64, (383:ℝ)/64, (425:ℝ)/64, (1478:ℝ)/64]
def jx24_leaf_04 : Fin 7 → ℤ := ![1, 3, 4, 5, 7, 8, 28]
theorem x24_leaf_04 (g : Fin 7 → ℝ)
    (hbox : ∀ i : Fin 7, lox24_leaf_04 i ≤ g i ∧ g i ≤ hix24_leaf_04 i) :
    Fresh.BandNoCarve.BandW1 g :=
  w1_of_faces (S := (520:ℝ)/53) (J := jx24_leaf_04) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> simp [lox24_leaf_04, hix24_leaf_04, jx24_leaf_04] <;> norm_num)
    hbox

#print axioms x24_leaf_04

/-- JSONL leaf D=64 n=[171, 231, 296, 381, 425, 1478], type fixedR0, carves [] -/
noncomputable def lox24_leaf_05 : Fin 7 → ℝ := ![1, (171:ℝ)/64, (231:ℝ)/64, (296:ℝ)/64, (381:ℝ)/64, (425:ℝ)/64, (1478:ℝ)/64]
noncomputable def hix24_leaf_05 : Fin 7 → ℝ := ![1, (172:ℝ)/64, (232:ℝ)/64, (297:ℝ)/64, (382:ℝ)/64, (426:ℝ)/64, (1479:ℝ)/64]
def jx24_leaf_05 : Fin 7 → ℤ := ![0, 1, 1, 2, 2, 3, 10]
theorem x24_leaf_05 (g : Fin 7 → ℝ)
    (hbox : ∀ i : Fin 7, lox24_leaf_05 i ≤ g i ∧ g i ≤ hix24_leaf_05 i) :
    Fresh.BandNoCarve.BandFixedR0 g :=
  ⟨⟨lox24_leaf_05, hix24_leaf_05, (64:ℝ)/17, jx24_leaf_05,
    by norm_num, by norm_num,
    by intro i; fin_cases i <;> simp [lox24_leaf_05, hix24_leaf_05] <;> norm_num,
    by intro i; fin_cases i <;> simp [lox24_leaf_05, hix24_leaf_05, jx24_leaf_05] <;> norm_num⟩,
   hbox⟩

#print axioms x24_leaf_05

/-- JSONL leaf D=64 n=[171, 231, 297, 381, 425, 1478], type fixedR0, carves [] -/
noncomputable def lox24_leaf_06 : Fin 7 → ℝ := ![1, (171:ℝ)/64, (231:ℝ)/64, (297:ℝ)/64, (381:ℝ)/64, (425:ℝ)/64, (1478:ℝ)/64]
noncomputable def hix24_leaf_06 : Fin 7 → ℝ := ![1, (172:ℝ)/64, (232:ℝ)/64, (298:ℝ)/64, (382:ℝ)/64, (426:ℝ)/64, (1479:ℝ)/64]
def jx24_leaf_06 : Fin 7 → ℤ := ![0, 1, 1, 2, 2, 3, 10]
theorem x24_leaf_06 (g : Fin 7 → ℝ)
    (hbox : ∀ i : Fin 7, lox24_leaf_06 i ≤ g i ∧ g i ≤ hix24_leaf_06 i) :
    Fresh.BandNoCarve.BandFixedR0 g :=
  ⟨⟨lox24_leaf_06, hix24_leaf_06, (64:ℝ)/17, jx24_leaf_06,
    by norm_num, by norm_num,
    by intro i; fin_cases i <;> simp [lox24_leaf_06, hix24_leaf_06] <;> norm_num,
    by intro i; fin_cases i <;> simp [lox24_leaf_06, hix24_leaf_06, jx24_leaf_06] <;> norm_num⟩,
   hbox⟩

#print axioms x24_leaf_06

/-- JSONL leaf D=64 n=[171, 231, 297, 382, 425, 1478], type fixedR0, carves [] -/
noncomputable def lox24_leaf_07 : Fin 7 → ℝ := ![1, (171:ℝ)/64, (231:ℝ)/64, (297:ℝ)/64, (382:ℝ)/64, (425:ℝ)/64, (1478:ℝ)/64]
noncomputable def hix24_leaf_07 : Fin 7 → ℝ := ![1, (172:ℝ)/64, (232:ℝ)/64, (298:ℝ)/64, (383:ℝ)/64, (426:ℝ)/64, (1479:ℝ)/64]
def jx24_leaf_07 : Fin 7 → ℤ := ![0, 1, 1, 2, 2, 3, 10]
theorem x24_leaf_07 (g : Fin 7 → ℝ)
    (hbox : ∀ i : Fin 7, lox24_leaf_07 i ≤ g i ∧ g i ≤ hix24_leaf_07 i) :
    Fresh.BandNoCarve.BandFixedR0 g :=
  ⟨⟨lox24_leaf_07, hix24_leaf_07, (64:ℝ)/17, jx24_leaf_07,
    by norm_num, by norm_num,
    by intro i; fin_cases i <;> simp [lox24_leaf_07, hix24_leaf_07] <;> norm_num,
    by intro i; fin_cases i <;> simp [lox24_leaf_07, hix24_leaf_07, jx24_leaf_07] <;> norm_num⟩,
   hbox⟩

#print axioms x24_leaf_07

/-- JSONL leaf D=64 n=[171, 231, 297, 383, 425, 1478], type fixedR0, carves [] -/
noncomputable def lox24_leaf_08 : Fin 7 → ℝ := ![1, (171:ℝ)/64, (231:ℝ)/64, (297:ℝ)/64, (383:ℝ)/64, (425:ℝ)/64, (1478:ℝ)/64]
noncomputable def hix24_leaf_08 : Fin 7 → ℝ := ![1, (172:ℝ)/64, (232:ℝ)/64, (298:ℝ)/64, (384:ℝ)/64, (426:ℝ)/64, (1479:ℝ)/64]
def jx24_leaf_08 : Fin 7 → ℤ := ![0, 1, 1, 2, 2, 3, 10]
theorem x24_leaf_08 (g : Fin 7 → ℝ)
    (hbox : ∀ i : Fin 7, lox24_leaf_08 i ≤ g i ∧ g i ≤ hix24_leaf_08 i) :
    Fresh.BandNoCarve.BandFixedR0 g :=
  ⟨⟨lox24_leaf_08, hix24_leaf_08, (64:ℝ)/17, jx24_leaf_08,
    by norm_num, by norm_num,
    by intro i; fin_cases i <;> simp [lox24_leaf_08, hix24_leaf_08] <;> norm_num,
    by intro i; fin_cases i <;> simp [lox24_leaf_08, hix24_leaf_08, jx24_leaf_08] <;> norm_num⟩,
   hbox⟩

#print axioms x24_leaf_08

/-- JSONL leaf D=64 n=[171, 231, 298, 381, 425, 1478], type fixedR0, carves [] -/
noncomputable def lox24_leaf_09 : Fin 7 → ℝ := ![1, (171:ℝ)/64, (231:ℝ)/64, (298:ℝ)/64, (381:ℝ)/64, (425:ℝ)/64, (1478:ℝ)/64]
noncomputable def hix24_leaf_09 : Fin 7 → ℝ := ![1, (172:ℝ)/64, (232:ℝ)/64, (299:ℝ)/64, (382:ℝ)/64, (426:ℝ)/64, (1479:ℝ)/64]
def jx24_leaf_09 : Fin 7 → ℤ := ![0, 1, 1, 2, 2, 3, 10]
theorem x24_leaf_09 (g : Fin 7 → ℝ)
    (hbox : ∀ i : Fin 7, lox24_leaf_09 i ≤ g i ∧ g i ≤ hix24_leaf_09 i) :
    Fresh.BandNoCarve.BandFixedR0 g :=
  ⟨⟨lox24_leaf_09, hix24_leaf_09, (64:ℝ)/17, jx24_leaf_09,
    by norm_num, by norm_num,
    by intro i; fin_cases i <;> simp [lox24_leaf_09, hix24_leaf_09] <;> norm_num,
    by intro i; fin_cases i <;> simp [lox24_leaf_09, hix24_leaf_09, jx24_leaf_09] <;> norm_num⟩,
   hbox⟩

#print axioms x24_leaf_09

/-- JSONL leaf D=64 n=[171, 231, 298, 382, 425, 1478], type fixedR0, carves [] -/
noncomputable def lox24_leaf_10 : Fin 7 → ℝ := ![1, (171:ℝ)/64, (231:ℝ)/64, (298:ℝ)/64, (382:ℝ)/64, (425:ℝ)/64, (1478:ℝ)/64]
noncomputable def hix24_leaf_10 : Fin 7 → ℝ := ![1, (172:ℝ)/64, (232:ℝ)/64, (299:ℝ)/64, (383:ℝ)/64, (426:ℝ)/64, (1479:ℝ)/64]
def jx24_leaf_10 : Fin 7 → ℤ := ![0, 1, 1, 2, 2, 3, 10]
theorem x24_leaf_10 (g : Fin 7 → ℝ)
    (hbox : ∀ i : Fin 7, lox24_leaf_10 i ≤ g i ∧ g i ≤ hix24_leaf_10 i) :
    Fresh.BandNoCarve.BandFixedR0 g :=
  ⟨⟨lox24_leaf_10, hix24_leaf_10, (64:ℝ)/17, jx24_leaf_10,
    by norm_num, by norm_num,
    by intro i; fin_cases i <;> simp [lox24_leaf_10, hix24_leaf_10] <;> norm_num,
    by intro i; fin_cases i <;> simp [lox24_leaf_10, hix24_leaf_10, jx24_leaf_10] <;> norm_num⟩,
   hbox⟩

#print axioms x24_leaf_10

/-- JSONL leaf D=64 n=[171, 231, 298, 383, 425, 1478], type fixedR0, carves [] -/
noncomputable def lox24_leaf_11 : Fin 7 → ℝ := ![1, (171:ℝ)/64, (231:ℝ)/64, (298:ℝ)/64, (383:ℝ)/64, (425:ℝ)/64, (1478:ℝ)/64]
noncomputable def hix24_leaf_11 : Fin 7 → ℝ := ![1, (172:ℝ)/64, (232:ℝ)/64, (299:ℝ)/64, (384:ℝ)/64, (426:ℝ)/64, (1479:ℝ)/64]
def jx24_leaf_11 : Fin 7 → ℤ := ![0, 1, 1, 2, 2, 3, 10]
theorem x24_leaf_11 (g : Fin 7 → ℝ)
    (hbox : ∀ i : Fin 7, lox24_leaf_11 i ≤ g i ∧ g i ≤ hix24_leaf_11 i) :
    Fresh.BandNoCarve.BandFixedR0 g :=
  ⟨⟨lox24_leaf_11, hix24_leaf_11, (64:ℝ)/17, jx24_leaf_11,
    by norm_num, by norm_num,
    by intro i; fin_cases i <;> simp [lox24_leaf_11, hix24_leaf_11] <;> norm_num,
    by intro i; fin_cases i <;> simp [lox24_leaf_11, hix24_leaf_11, jx24_leaf_11] <;> norm_num⟩,
   hbox⟩

#print axioms x24_leaf_11

/-- JSONL leaf D=64 n=[171, 231, 295, 380, 421, 1472], type w1, carves [] -/
noncomputable def lox24_leaf_12 : Fin 7 → ℝ := ![1, (171:ℝ)/64, (231:ℝ)/64, (295:ℝ)/64, (380:ℝ)/64, (421:ℝ)/64, (1472:ℝ)/64]
noncomputable def hix24_leaf_12 : Fin 7 → ℝ := ![1, (172:ℝ)/64, (232:ℝ)/64, (296:ℝ)/64, (381:ℝ)/64, (422:ℝ)/64, (1473:ℝ)/64]
def jx24_leaf_12 : Fin 7 → ℤ := ![1, 3, 4, 5, 7, 8, 28]
theorem x24_leaf_12 (g : Fin 7 → ℝ)
    (hbox : ∀ i : Fin 7, lox24_leaf_12 i ≤ g i ∧ g i ≤ hix24_leaf_12 i) :
    Fresh.BandNoCarve.BandW1 g :=
  w1_of_faces (S := (4160:ℝ)/421) (J := jx24_leaf_12) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> simp [lox24_leaf_12, hix24_leaf_12, jx24_leaf_12] <;> norm_num)
    hbox

#print axioms x24_leaf_12

/-- JSONL leaf D=64 n=[171, 231, 295, 380, 421, 1473], type w1, carves [] -/
noncomputable def lox24_leaf_13 : Fin 7 → ℝ := ![1, (171:ℝ)/64, (231:ℝ)/64, (295:ℝ)/64, (380:ℝ)/64, (421:ℝ)/64, (1473:ℝ)/64]
noncomputable def hix24_leaf_13 : Fin 7 → ℝ := ![1, (172:ℝ)/64, (232:ℝ)/64, (296:ℝ)/64, (381:ℝ)/64, (422:ℝ)/64, (1474:ℝ)/64]
def jx24_leaf_13 : Fin 7 → ℤ := ![1, 3, 4, 5, 7, 8, 28]
theorem x24_leaf_13 (g : Fin 7 → ℝ)
    (hbox : ∀ i : Fin 7, lox24_leaf_13 i ≤ g i ∧ g i ≤ hix24_leaf_13 i) :
    Fresh.BandNoCarve.BandW1 g :=
  w1_of_faces (S := (4160:ℝ)/421) (J := jx24_leaf_13) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> simp [lox24_leaf_13, hix24_leaf_13, jx24_leaf_13] <;> norm_num)
    hbox

#print axioms x24_leaf_13

/-- JSONL leaf D=64 n=[171, 231, 295, 380, 421, 1474], type w1, carves [] -/
noncomputable def lox24_leaf_14 : Fin 7 → ℝ := ![1, (171:ℝ)/64, (231:ℝ)/64, (295:ℝ)/64, (380:ℝ)/64, (421:ℝ)/64, (1474:ℝ)/64]
noncomputable def hix24_leaf_14 : Fin 7 → ℝ := ![1, (172:ℝ)/64, (232:ℝ)/64, (296:ℝ)/64, (381:ℝ)/64, (422:ℝ)/64, (1475:ℝ)/64]
def jx24_leaf_14 : Fin 7 → ℤ := ![1, 3, 4, 5, 7, 8, 28]
theorem x24_leaf_14 (g : Fin 7 → ℝ)
    (hbox : ∀ i : Fin 7, lox24_leaf_14 i ≤ g i ∧ g i ≤ hix24_leaf_14 i) :
    Fresh.BandNoCarve.BandW1 g :=
  w1_of_faces (S := (4160:ℝ)/421) (J := jx24_leaf_14) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> simp [lox24_leaf_14, hix24_leaf_14, jx24_leaf_14] <;> norm_num)
    hbox

#print axioms x24_leaf_14

/-- JSONL leaf D=64 n=[171, 231, 295, 380, 422, 1472], type w1, carves [] -/
noncomputable def lox24_leaf_15 : Fin 7 → ℝ := ![1, (171:ℝ)/64, (231:ℝ)/64, (295:ℝ)/64, (380:ℝ)/64, (422:ℝ)/64, (1472:ℝ)/64]
noncomputable def hix24_leaf_15 : Fin 7 → ℝ := ![1, (172:ℝ)/64, (232:ℝ)/64, (296:ℝ)/64, (381:ℝ)/64, (423:ℝ)/64, (1473:ℝ)/64]
def jx24_leaf_15 : Fin 7 → ℤ := ![1, 3, 4, 5, 7, 8, 28]
theorem x24_leaf_15 (g : Fin 7 → ℝ)
    (hbox : ∀ i : Fin 7, lox24_leaf_15 i ≤ g i ∧ g i ≤ hix24_leaf_15 i) :
    Fresh.BandNoCarve.BandW1 g :=
  w1_of_faces (S := (2080:ℝ)/211) (J := jx24_leaf_15) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> simp [lox24_leaf_15, hix24_leaf_15, jx24_leaf_15] <;> norm_num)
    hbox

#print axioms x24_leaf_15

/-- JSONL leaf D=64 n=[171, 231, 295, 380, 422, 1473], type w1, carves [] -/
noncomputable def lox24_leaf_16 : Fin 7 → ℝ := ![1, (171:ℝ)/64, (231:ℝ)/64, (295:ℝ)/64, (380:ℝ)/64, (422:ℝ)/64, (1473:ℝ)/64]
noncomputable def hix24_leaf_16 : Fin 7 → ℝ := ![1, (172:ℝ)/64, (232:ℝ)/64, (296:ℝ)/64, (381:ℝ)/64, (423:ℝ)/64, (1474:ℝ)/64]
def jx24_leaf_16 : Fin 7 → ℤ := ![1, 3, 4, 5, 7, 8, 28]
theorem x24_leaf_16 (g : Fin 7 → ℝ)
    (hbox : ∀ i : Fin 7, lox24_leaf_16 i ≤ g i ∧ g i ≤ hix24_leaf_16 i) :
    Fresh.BandNoCarve.BandW1 g :=
  w1_of_faces (S := (2080:ℝ)/211) (J := jx24_leaf_16) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> simp [lox24_leaf_16, hix24_leaf_16, jx24_leaf_16] <;> norm_num)
    hbox

#print axioms x24_leaf_16

/-- JSONL leaf D=64 n=[171, 231, 295, 380, 422, 1474], type w1, carves [] -/
noncomputable def lox24_leaf_17 : Fin 7 → ℝ := ![1, (171:ℝ)/64, (231:ℝ)/64, (295:ℝ)/64, (380:ℝ)/64, (422:ℝ)/64, (1474:ℝ)/64]
noncomputable def hix24_leaf_17 : Fin 7 → ℝ := ![1, (172:ℝ)/64, (232:ℝ)/64, (296:ℝ)/64, (381:ℝ)/64, (423:ℝ)/64, (1475:ℝ)/64]
def jx24_leaf_17 : Fin 7 → ℤ := ![1, 3, 4, 5, 7, 8, 28]
theorem x24_leaf_17 (g : Fin 7 → ℝ)
    (hbox : ∀ i : Fin 7, lox24_leaf_17 i ≤ g i ∧ g i ≤ hix24_leaf_17 i) :
    Fresh.BandNoCarve.BandW1 g :=
  w1_of_faces (S := (2080:ℝ)/211) (J := jx24_leaf_17) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> simp [lox24_leaf_17, hix24_leaf_17, jx24_leaf_17] <;> norm_num)
    hbox

#print axioms x24_leaf_17

/-- JSONL leaf D=64 n=[171, 231, 295, 380, 423, 1472], type w1, carves [] -/
noncomputable def lox24_leaf_18 : Fin 7 → ℝ := ![1, (171:ℝ)/64, (231:ℝ)/64, (295:ℝ)/64, (380:ℝ)/64, (423:ℝ)/64, (1472:ℝ)/64]
noncomputable def hix24_leaf_18 : Fin 7 → ℝ := ![1, (172:ℝ)/64, (232:ℝ)/64, (296:ℝ)/64, (381:ℝ)/64, (424:ℝ)/64, (1473:ℝ)/64]
def jx24_leaf_18 : Fin 7 → ℤ := ![1, 3, 4, 5, 7, 8, 28]
theorem x24_leaf_18 (g : Fin 7 → ℝ)
    (hbox : ∀ i : Fin 7, lox24_leaf_18 i ≤ g i ∧ g i ≤ hix24_leaf_18 i) :
    Fresh.BandNoCarve.BandW1 g :=
  w1_of_faces (S := (4160:ℝ)/423) (J := jx24_leaf_18) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> simp [lox24_leaf_18, hix24_leaf_18, jx24_leaf_18] <;> norm_num)
    hbox

#print axioms x24_leaf_18

end Fresh.X24Pilot
