import Fresh.FilterAssembly

/-!
# The covering half of the pinned tail lemma: the anchor classification and the gap regimes

Provenance: `experiments/n8/tailrest_anchor_lemma_v1.out` (the anchor-classification lemma,
validated [T 105/105] on the recorded population), `tailrest_composition_v1.out` (the
composition T1–T6 and the residue ledger), `tailrest_gapcover_v1/v2.out`.  Formalized
2026-11-14; new file, nothing existing is edited.

SETTING (R-coordinates, readings normalised with ρ₁ = 1).  The readings are
`g : Fin 7 → ℝ` with `g 0 = ρ₁ = 1 ≤ ρ₂ ≤ … ≤ ρ₇ = g 6` (`Monotone g`), and a carve of
`[1,7]` is `Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ)`: every
`R ∈ [1,7]` lies in some reading's open zone `8j−1 < ρR < 8j+1`.  Since the union must
contain the point `R = 1`, a carve forces a reading value `ρ` with `8j−1 < ρ·1 < 8j+1`,
i.e. `ρ` in the open strip `C_j = (8j−1, 8j+1)` (`InStrip` — the comb fact E839 L1; this is
the reading-coordinate form of `Fresh.UClosureKill.InZone` at the window point `R`).

CONTENT.
* `notInStrip_of_le_seven` — the pin kills every reading but ρ₇: a reading in `[1,7]` lies
  in no strip (`C₁ = (7,9)` is open at exactly 7; `C₀ = (−1,1)` is open at 1).
* `anchor_classification` — TARGET 1: under the pin (`ρ₆ ≤ 49/7 = 7`) the `R = 1` coverer
  is `∅` or the singleton `{(ρ₇, j)}` — self-anchored, with the lap forced by strip
  disjointness (`InStrip_unique`).
* `gap_carve_free` — TARGET 2: under the pin, ρ₇ in an open gap `G_m = (8m+1, 8m+7)` (ANY
  `m`) leaves `R = 1` uncovered, hence no carve — every pinned gap regime dies in one comb
  argument, no chase and no walk (composition piece T3).
* `pinnedCarve_selfAnchor` — corollary C1: every carve with ρ₇ ≥ 25 is ρ₇-self-anchored
  with forced lap `j ≥ 4`, so the pinned tail reduces to the strips `m ≥ 4`.
* `pinnedTail_noCarve` — TARGET 3: the composition T3+T4+T5 — under the pin, no carve with
  ρ₇ ≥ 25, given the strip kills `C₄, C₅, C₆` (the completed chases, hypothesis
  `StripChaseKill46`) and `ρ₇ ≥ 50` (the covering session's width certificate, hypothesis
  `TailAbove50Cover`).  The gap regimes and the strip edges need no hypothesis: a carve
  forces ρ₇ into some `C_j` with `j ≥ 4`, and every such `j` is either in `{4,5,6}` (killed
  by the chases) or puts ρ₇ ≥ 55 (killed by T5).  The mission phrasing "ρ₇ ≥ 25 outside
  (23,25)" is subsumed: X24 = (23, 86989/3565) ⊂ (23,25) is already excluded by ρ₇ ≥ 25.
* `pinnedCarveLocus_of_census_and_caps` — the residue form: with the cap-half census (E839
  item 2) and the two attained strip caps (T1/T2, hypotheses), the pinned carve locus is
  contained in `(15, 511/31] ∪ (23, 86989/3565]`.

OWEDs (named, rule 7): `StripChaseKill46` (T4 — the chase ledger's exact kills
`midbound_chase_v1/v2` are data-side, `feas_types = 0`, `complete = True`),
`TailAbove50Cover` (T5 — `Fresh.TailStrip49.bandClearPoint_of_slow_cap17` exists but
replays its width check via `native_decide`, whose `Lean.ofReduceBool` is outside this
file's axiom discipline; the `NoCarve`-form instrument is owed),
`PinnedCensusStrips23` and the caps of `pinnedCarveLocus_of_census_and_caps` (T1/T2, the
cap-half instruments), and `PinnedTailCover` (the composed tail lemma's covering side,
discharged by `pinnedTailCover_of_instruments`).

The unpinned regimes (ρ₆ > 7) are NOT claimed here: residues R2/R3 of
`tailrest_composition_v1.out` stay open, and the anchor lemma narrows nothing — the
unpinned gap regime is explicitly not dead on this evidence.
-/

namespace Fresh.BandTailCover

open Fresh Fresh.Cascade

/-! ## Strip vocabulary and the comb fact at `R = 1` -/

/-- The open strip `C_j = (8j−1, 8j+1)` in reading coordinates: reading value `ρ` lies in
strip `j` exactly when reading `ρ`'s lap-`j` zone covers `R = 1` (the `CarvesOneSeven`
membership form at `R = 1`, `8j−1 < ρ·1 < 8j+1`). -/
-- STANDING: DEFINITION
def InStrip (ρ : ℝ) (j : ℤ) : Prop :=
  ((8 * j - 1 : ℤ) : ℝ) < ρ ∧ ρ < ((8 * j + 1 : ℤ) : ℝ)

theorem cast_edge_lo (j : ℤ) : ((8 * j - 1 : ℤ) : ℝ) = (j : ℝ) * 8 - 1 := by
  push_cast
  ring

theorem cast_edge_hi (j : ℤ) : ((8 * j + 1 : ℤ) : ℝ) = (j : ℝ) * 8 + 1 := by
  push_cast
  ring

/-- The strip membership unpacked (definitional). -/
theorem inStrip_iff {ρ : ℝ} {j : ℤ} :
    InStrip ρ j ↔ ((8 * j - 1 : ℤ) : ℝ) < ρ ∧ ρ < ((8 * j + 1 : ℤ) : ℝ) := Iff.rfl

/-- The comb fact E839 L1 at `R = 1`: reading `ρ`'s lap-`j` zone covers `R = 1` iff
`ρ ∈ C_j`. -/
theorem zoneAtOne_iff {ρ : ℝ} {j : ℤ} :
    ((j : ℝ) * 8 - 1 < ρ * 1 ∧ ρ * 1 < (j : ℝ) * 8 + 1) ↔ InStrip ρ j := by
  simp only [InStrip, cast_edge_lo, cast_edge_hi, mul_one]

#print axioms zoneAtOne_iff

/-- **The comb fact at the pin** (tailrest_anchor_lemma_v1 (i)): a reading in `[1,7]` lies
in no strip — `C₁ = (7,9)` is open at exactly 7, every higher strip has lower edge
`8j−1 ≥ 7`, and `C₀ = (−1,1)` is open at 1. -/
theorem notInStrip_of_le_seven {ρ : ℝ} (h1 : (1 : ℝ) ≤ ρ) (h7 : ρ ≤ 7) (j : ℤ) :
    ¬ InStrip ρ j := by
  intro hcon
  obtain ⟨hlo, hhi⟩ := hcon
  rcases lt_or_ge j 1 with hj | hj
  · exfalso
    have hz : (8 * j + 1 : ℤ) ≤ 1 := by omega
    have hr : ((8 * j + 1 : ℤ) : ℝ) ≤ (1 : ℝ) := by exact_mod_cast hz
    linarith
  · exfalso
    have hz : (7 : ℤ) ≤ 8 * j - 1 := by omega
    have hr : (7 : ℝ) ≤ ((8 * j - 1 : ℤ) : ℝ) := by exact_mod_cast hz
    linarith

#print axioms notInStrip_of_le_seven

/-- **The gap fact** (tailrest_anchor_lemma_v1 (ii)): a reading in the open gap
`G_m = (8m+1, 8m+7)` lies in no strip — the strips have width 2 and spacing 8, so `G_m`
touches only `C_m` (open at `8m+1`) and `C_{m+1}` (open at `8m+7`). -/
theorem notInStrip_of_gap {ρ : ℝ} {m : ℤ}
    (hgap : ((8 * m + 1 : ℤ) : ℝ) < ρ ∧ ρ < ((8 * m + 7 : ℤ) : ℝ)) (j : ℤ) :
    ¬ InStrip ρ j := by
  intro hcon
  obtain ⟨hlo, hhi⟩ := hcon
  have h1 : (8 * j - 1 : ℤ) < 8 * m + 7 :=
    Int.cast_lt.mp (lt_trans hlo hgap.2)
  have h2 : (8 * m + 1 : ℤ) < 8 * j + 1 :=
    Int.cast_lt.mp (lt_trans hgap.1 hhi)
  omega

#print axioms notInStrip_of_gap

/-- **Strip disjointness** (the forced lap): a reading value lies in at most one strip, so
a strip zone covering `R = 1` has a unique lap. -/
theorem InStrip_unique {ρ : ℝ} {j j' : ℤ} (h : InStrip ρ j) (h' : InStrip ρ j') :
    j = j' := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  rcases lt_trichotomy j j' with hj | hj | hj
  · exfalso
    have hz : (8 * j + 1 : ℤ) ≤ 8 * j' - 1 := by omega
    have hle : ((8 * j + 1 : ℤ) : ℝ) ≤ ((8 * j' - 1 : ℤ) : ℝ) := by exact_mod_cast hz
    linarith
  · exact hj
  · exfalso
    have hz : (8 * j' + 1 : ℤ) ≤ 8 * j - 1 := by omega
    have hle : ((8 * j' + 1 : ℤ) : ℝ) ≤ ((8 * j - 1 : ℤ) : ℝ) := by exact_mod_cast hz
    linarith

#print axioms InStrip_unique

/-! ## The pinned tuple: the readings below the last cover nothing at `R = 1` -/

/-- Under the ordering and the pin (`ρ₆ = g 5 ≤ 49/7 = 7`), every reading `ρᵢ` with
`i ≤ 5` is at most 7. -/
theorem g_le_seven_of_le_five {g : Fin 7 → ℝ} (ordered : Monotone g) (hpin : g 5 ≤ 7)
    {i : Fin 7} (hi : i.val ≤ 5) : g i ≤ 7 :=
  (ordered (Fin.le_iff_val_le_val.mpr hi)).trans hpin

/-- Under the pin, reading `ρᵢ` for `i ≤ 5` lies in no strip: its zone covers `R = 1` at
no lap (the first half of the anchor classification — readings ρ₂..ρ₆ cannot cover). -/
theorem noCover_of_pinned {g : Fin 7 → ℝ}
    (pin : g 0 = 1) (ordered : Monotone g) (hpin : g 5 ≤ 7)
    {i : Fin 7} (hi : i.val ≤ 5) (j : ℤ) : ¬ InStrip (g i) j := by
  have h1i : (1 : ℝ) ≤ g i := by
    have h0i := ordered (Fin.zero_le i)
    rw [pin] at h0i
    exact h0i
  exact notInStrip_of_le_seven h1i (g_le_seven_of_le_five ordered hpin hi) j

#print axioms noCover_of_pinned

/-! ## TARGET 1: the anchor classification -/

/-- **The anchor classification** (tailrest_anchor_lemma_v1, pinned form (i)): under the
pin (`ρ₆ ≤ 49/7 = 7`, with `ρ₁ = 1` and ordered readings), a strip zone covering `R = 1`
belongs to the last reading `ρ₇` alone and its lap is forced: the `R = 1` coverer is `∅`
or the singleton `{(ρ₇, j)}` — self-anchored, with a forced lap. -/
theorem anchor_classification {g : Fin 7 → ℝ}
    (pin : g 0 = 1) (ordered : Monotone g) (hpin : g 5 ≤ 7)
    {i : Fin 7} {j : ℤ} (h : InStrip (g i) j) :
    i.val = 6 ∧ ∀ j' : ℤ, InStrip (g 6) j' → j' = j := by
  have h6 : i.val = 6 := by
    by_contra hne
    have hi5 : i.val ≤ 5 := by have := i.isLt; omega
    exact noCover_of_pinned pin ordered hpin hi5 j h
  refine ⟨h6, ?_⟩
  have hiE : i = 6 := Fin.val_injective h6
  subst hiE
  intro j' h'
  exact InStrip_unique h' h

#print axioms anchor_classification

/-! ## TARGET 2: the gap-regime corollary — no carve in any pinned gap -/

/-- **The gap-regime corollary** (tailrest_anchor_lemma_v1 (ii); composition piece T3):
under the pin, ρ₇ in the open gap `G_m = (8m+1, 8m+7)` leaves `R = 1` uncovered — no
reading's zone contains it — hence there is no carve of `[1,7]`.  This kills every pinned
gap regime at EVERY `m` in one comb argument (no chase, no walk); in particular the tail
gaps `G_m`, `m ≥ 3`: (25,31), (33,39), …. -/
theorem gap_carve_free {g : Fin 7 → ℝ}
    (pin : g 0 = 1) (ordered : Monotone g) (hpin : g 5 ≤ 7) {m : ℤ}
    (hgap : ((8 * m + 1 : ℤ) : ℝ) < g 6 ∧ g 6 < ((8 * m + 7 : ℤ) : ℝ)) :
    Fresh.Certs.NoCarve g := by
  intro hcarve
  obtain ⟨ρ, hρmem, j, hj1, hj2⟩ := hcarve 1 (by norm_num) (by norm_num)
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hρmem
  have hz : InStrip (g i) j := zoneAtOne_iff.mp ⟨hj1, hj2⟩
  rcases Nat.lt_or_ge i.val 6 with hi | hi
  · exact absurd hz
      (noCover_of_pinned pin ordered hpin (by have := i.isLt; omega) j)
  · have hiE : i = 6 := Fin.val_injective (by have := i.isLt; omega)
    subst hiE
    exact absurd hz (notInStrip_of_gap hgap j)

#print axioms gap_carve_free

/-! ## Corollary C1: pinned carves with ρ₇ ≥ 25 are self-anchored at a lap ≥ 4 -/

/-- **Corollary C1** (pinned tail, the cap half's hypothesis in force): every carve with
ρ₇ ≥ 25 is ρ₇-self-anchored with a forced lap `j ≥ 4` — the pinned tail reduces to the
strips `C_m`, `m ≥ 4`, exactly the chase / middle-service setting. -/
theorem pinnedCarve_selfAnchor {g : Fin 7 → ℝ}
    (pin : g 0 = 1) (ordered : Monotone g) (hpin : g 5 ≤ 7)
    (hcarve : Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ))
    (h25 : (25 : ℝ) ≤ g 6) :
    ∃ j : ℤ, 4 ≤ j ∧ ((8 * j - 1 : ℤ) : ℝ) < g 6 ∧ g 6 < ((8 * j + 1 : ℤ) : ℝ) := by
  obtain ⟨ρ, hρmem, j, hj1, hj2⟩ := hcarve 1 (by norm_num) (by norm_num)
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hρmem
  have hz : InStrip (g i) j := zoneAtOne_iff.mp ⟨hj1, hj2⟩
  rcases Nat.lt_or_ge i.val 6 with hi | hi
  · exact absurd hz
      (noCover_of_pinned pin ordered hpin (by have := i.isLt; omega) j)
  · have hiE : i = 6 := Fin.val_injective (by have := i.isLt; omega)
    subst hiE
    refine ⟨j, ?_, (inStrip_iff.mp hz).1, (inStrip_iff.mp hz).2⟩
    have hzr := (inStrip_iff.mp hz).2
    push_cast at hzr
    have hr : ((24 : ℤ) : ℝ) < ((8 * j : ℤ) : ℝ) := by
      push_cast
      linarith
    have h4 : (4 : ℤ) ≤ j := by
      have hz1 : (24 : ℤ) < 8 * j := Int.cast_lt.mp hr
      omega
    exact h4

#print axioms pinnedCarve_selfAnchor

/-! ## The certificate-side bridge -/

/-- A clear point `R₀ ∈ [1,7]` — every reading's `ρR₀` in a closed gap `[8j+1, 8j+7]` —
excludes carving: the certificate-soundness bridge, the reverse of
`Fresh.BandNoCarve.clearPoint_of_noCarve` (a witness contradicts the carve at the witness
point). -/
theorem noCarve_of_clearWitness {g : Fin 7 → ℝ} {R₀ : ℝ}
    (h1 : (1 : ℝ) ≤ R₀) (h7 : R₀ ≤ 7)
    (hcl : ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (R₀ / 8))) :
    Fresh.Certs.NoCarve g := by
  intro hcarve
  obtain ⟨ρ, hρmem, j, hj1, hj2⟩ := hcarve R₀ h1 h7
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hρmem
  exact (not_inWay_iff.mpr (hcl i)) (Fresh.Certs.inWay_of_zone (j := j)
    (by push_cast; linarith) (by push_cast; linarith))

#print axioms noCarve_of_clearWitness

/-! ## TARGET 3: the composition — no pinned carve with ρ₇ ≥ 25 -/

/-- **OWED (T4, data-side)**: the completed chases of `midbound_chase_v1/v2` — strips
`C₄ = (31,33)`, `C₅ = (39,41)`, `C₆ = (47,49)` killed, `feas_types = 0`, `complete = True`
(248s / 687s / 1782s) — as a Lean statement.  The chase ledger is exact but computational;
the Lean-form theorem is owed. -/
-- STANDING: OWED
def StripChaseKill46 : Prop :=
  ∀ g : Fin 7 → ℝ, g 0 = 1 → Monotone g → g 5 ≤ 7 →
    ∀ m : ℤ, 4 ≤ m → m ≤ 6 → InStrip (g 6) m → Fresh.Certs.NoCarve g

/-- **OWED (T5, [PROVISIONAL: covering])**: the covering session's width certificate
(`Fresh.TailStrip49.bandClearPoint_of_slow_cap17`'s first-window half) in `NoCarve` form
for ρ₇ ≥ 50 under the pin.  `bandClearPoint_of_slow_cap17` exists but its width check
replays via `native_decide` (`Lean.ofReduceBool`), outside this file's axiom discipline;
its clear point also lands in `W₀ ∪ W₁` (`s ≤ 7 ∨ 9 ≤ s`), and only the `s ≤ 7` branch
discharges a `NoCarve` of `[1,7]`. -/
-- STANDING: OWED
def TailAbove50Cover : Prop :=
  ∀ g : Fin 7 → ℝ, g 0 = 1 → Monotone g → g 5 ≤ 7 → (50 : ℝ) ≤ g 6 → Fresh.Certs.NoCarve g

/-- **OWED (the tail lemma, covering side)**: no carve of `[1,7]` with ρ₇ ≥ 25 under the
pin — composed here from the comb (gaps, proved), `StripChaseKill46` (strips 4–6) and
`TailAbove50Cover` (ρ₇ ≥ 50). -/
-- STANDING: OWED
def PinnedTailCover : Prop :=
  ∀ g : Fin 7 → ℝ, g 0 = 1 → Monotone g → g 5 ≤ 7 → (25 : ℝ) ≤ g 6 → Fresh.Certs.NoCarve g

/-- **The composition (tailrest_composition_v1, pieces T3+T4+T5)**: under the pin with
ρ₇ ≥ 25, no carve.  Proof shape: a carve forces (by the anchor classification) a
ρ₇-self-anchor `InStrip (g 6) j` with `j ≥ 4`; then `j ≤ 6` (when ρ₇ < 50) hands the strip
to the chase kills, and `j ≥ 7` puts ρ₇ ≥ 55 ≥ 50, handed to the covering certificate.
The gaps and the strip edges in `[25,50)` need no hypothesis — a carve forces ρ₇ into a
strip, which the gap/edge facts (`gap_carve_free`, the comb) forbid. -/
theorem pinnedTail_noCarve {g : Fin 7 → ℝ}
    (pin : g 0 = 1) (ordered : Monotone g) (hpin : g 5 ≤ 7)
    (hS : ∀ m : ℤ, 4 ≤ m → m ≤ 6 → InStrip (g 6) m → Fresh.Certs.NoCarve g)
    (hT5 : (50 : ℝ) ≤ g 6 → Fresh.Certs.NoCarve g)
    (h25 : (25 : ℝ) ≤ g 6) :
    Fresh.Certs.NoCarve g := by
  intro hcarve
  by_cases h50 : (50 : ℝ) ≤ g 6
  · exact absurd hcarve (hT5 h50)
  · have h50' : g 6 < (50 : ℝ) := lt_of_not_ge h50
    obtain ⟨j, hj4, hj1, hj2⟩ := pinnedCarve_selfAnchor pin ordered hpin hcarve h25
    have h6 : j ≤ 6 := by
      have hr : ((8 * j : ℤ) : ℝ) < ((51 : ℤ) : ℝ) := by
        have hj1' := hj1
        push_cast at hj1'
        push_cast
        linarith
      have hz1 : (8 * j : ℤ) < 51 := Int.cast_lt.mp hr
      omega
    exact absurd hcarve (hS j hj4 h6 (inStrip_iff.mpr ⟨hj1, hj2⟩))

#print axioms pinnedTail_noCarve

/-- The composed tail lemma's covering side, discharged from the two strip instruments
(the gap side needs no instrument — it is the comb, `gap_carve_free`). -/
theorem pinnedTailCover_of_instruments (hS : StripChaseKill46) (hT5 : TailAbove50Cover) :
    PinnedTailCover := by
  intro g pin ordered hpin h25
  exact pinnedTail_noCarve pin ordered hpin
    (fun m h4 h6 hstrip => hS g pin ordered hpin m h4 h6 hstrip)
    (fun h50 => hT5 g pin ordered hpin h50) h25

#print axioms pinnedTailCover_of_instruments

/-! ## The residue form: the pinned carve locus under the census and the two caps -/

/-- **OWED (cap-half census, E839 item 2)**: under the pin, carves occur only in strips 2
and 3 — the recorded regime census (96/96 carves: strip 2 ×6, strip 3 ×90). -/
-- STANDING: OWED
def PinnedCensusStrips23 : Prop :=
  ∀ g : Fin 7 → ℝ, g 0 = 1 → Monotone g → g 5 ≤ 7 →
    Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ) →
      ((15 : ℝ) < g 6 ∧ g 6 < 17) ∨ ((23 : ℝ) < g 6 ∧ g 6 < 25)

/-- **The composed carve locus** (tailrest_composition_v1, corollary): under the pin, the
carve locus is contained in `(15, 511/31] ∪ (23, 86989/3565]` — the census plus the two
attained strip caps (T1: cap `511/31 = (73/31)(49/7)`, the m=2 cap type alive at the cap;
T2: cap `86989/3565`, X24, attained) — with every gap and everything past 25 already
killed here by the comb (`gap_carve_free`, `pinnedTail_noCarve`). -/
theorem pinnedCarveLocus_of_census_and_caps
    (hCensus : PinnedCensusStrips23)
    (hCap2 : ∀ g : Fin 7 → ℝ, g 0 = 1 → Monotone g → g 5 ≤ 7 →
      Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ) →
        (15 : ℝ) < g 6 → g 6 < 17 → g 6 ≤ 511 / 31)
    (hCap3 : ∀ g : Fin 7 → ℝ, g 0 = 1 → Monotone g → g 5 ≤ 7 →
      Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ) →
        (23 : ℝ) < g 6 → g 6 < 25 → g 6 ≤ 86989 / 3565)
    (g : Fin 7 → ℝ) (pin : g 0 = 1) (ordered : Monotone g) (hpin : g 5 ≤ 7)
    (hcarve : Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ)) :
    ((15 : ℝ) < g 6 ∧ g 6 ≤ 511 / 31) ∨ ((23 : ℝ) < g 6 ∧ g 6 ≤ 86989 / 3565) := by
  rcases hCensus g pin ordered hpin hcarve with ⟨h15, h17⟩ | ⟨h23, h25⟩
  · exact Or.inl ⟨h15, hCap2 g pin ordered hpin hcarve h15 h17⟩
  · exact Or.inr ⟨h23, hCap3 g pin ordered hpin hcarve h23 h25⟩

#print axioms pinnedCarveLocus_of_census_and_caps

end Fresh.BandTailCover
