-- Axiom check for every theorem of Construction8 (for MANUSCRIPT_v9). Run from LonelyRunner/: lake env lean ../experiments/n8/v9_construction8_all_axioms_v1.lean
import LonelyRunner.LRC.Construction8.Parts
import LonelyRunner.LRC.Construction8.LemmaPass
import LonelyRunner.LRC.Construction8.Coords
import LonelyRunner.LRC.Construction8.Reference
import LonelyRunner.LRC.Construction8.Gaps
import LonelyRunner.LRC.Construction8.Sorted
import LonelyRunner.LRC.Construction8.Grid
import LonelyRunner.LRC.Construction8.Integrality
import LonelyRunner.LRC.Construction8.Flank
import LonelyRunner.LRC.Construction8.Window
import LonelyRunner.LRC.Construction8.Bounds
#print axioms Construction8.ratio_condition
#print axioms Construction8.eq_univ_of_pred_closed
#print axioms Construction8.lonely_ne_pred
#print axioms Construction8.wide_gap_speeds
#print axioms Construction8.coord_iff
#print axioms Construction8.stretch_overlap
#print axioms Construction8.first_stretch_overlap
#print axioms Construction8.consecutive_break
#print axioms Construction8.wide_gap_core
#print axioms Construction8.wide_gap_end
#print axioms Construction8.blocked_width
#print axioms Construction8.clear_width
#print axioms Construction8.no_solo_closure
#print axioms Construction8.solo_closure_forces_smaller
#print axioms Construction8.circDist_of_abs_lt_one
#print axioms Construction8.circDist_ge_flank
#print axioms Construction8.lonely_of_flanks
#print axioms Construction8.circDist_ge_flank_first
#print axioms Construction8.circDist_ge_flank_last
#print axioms Construction8.lonely_of_flanks_first
#print axioms Construction8.lonely_of_flanks_last
#print axioms Construction8.one_sub_ge_of_circDist
#print axioms Construction8.flanks_of_lonely
#print axioms Construction8.flanks_of_lonely_first
#print axioms Construction8.flanks_of_lonely_last
#print axioms Construction8.lonely_iff_flanks
#print axioms Construction8.lonely_iff_flanks_first
#print axioms Construction8.lonely_iff_flanks_last
#print axioms Construction8.cycGap_sum_range
#print axioms Construction8.cycGap_sum
#print axioms Construction8.cycGap_all_eq
#print axioms Construction8.circDist_wrap
#print axioms Construction8.cycGap_ge_of_adjacent
#print axioms Construction8.cycGap_eq_of_adjacent
#print axioms Construction8.sorted_eq_grid
#print axioms Construction8.cycGap_interior
#print axioms Construction8.grid_of_pairwise
#print axioms Construction8.exists_sorted_index
#print axioms Construction8.sortedPos_zero_le
#print axioms Construction8.sortedPos_zero_eq
#print axioms Construction8.pos_eq_multiple
#print axioms Construction8.int_of_fract_multiple
#print axioms Construction8.circDist_fract_sub
#print axioms Construction8.int_of_pairwise_sep
#print axioms Construction8.not_dvd_of_sep
#print axioms Construction8.le_of_le_circDist
#print axioms Construction8.step_ceiling
#print axioms Construction8.commensurable
#print axioms Construction8.dead_iff
#print axioms Construction8.dead_downward
#print axioms Construction8.exists_live
#print axioms Construction8.clear_on_left
#print axioms Construction8.opening_le
#print axioms Construction8.reading_complete
#print axioms Construction8.circDist_int_div
#print axioms Construction8.ap_pair_clear
#print axioms Construction8.clearing_needs
#print axioms Construction8.reach_lower
#print axioms Construction8.reach_upper
#print axioms Construction8.circDist_add_int
#print axioms Construction8.clear_periodic
#print axioms Construction8.periodic_meets
#print axioms Construction8.window_length
#print axioms Construction8.run_identity
#print axioms Construction8.circDist_int_div_of_dvd
#print axioms Construction8.spine_all_or_nothing
#print axioms Construction8.localisation_free
#print axioms Construction8.blocked_lands_on_threshold
#print axioms Construction8.unblocked_stays_clear
#print axioms Construction8.gaps_all_eq
#print axioms Construction8.nearest_below
#print axioms Construction8.nearest_above
#print axioms Construction8.before_floor
#print axioms Construction8.displacement
#print axioms Construction8.ap_separation
#print axioms Construction8.ap_reference
#print axioms Construction8.deviation_separation
#print axioms Construction8.survives_of
#print axioms Construction8.sortedPos_apply
#print axioms Construction8.cycGap_sortedPos_sep
#print axioms Construction8.cycGap_sortedPos_nonneg
#print axioms Construction8.equally_spaced_of_pairwise
#print axioms Construction8.window_iff
#print axioms Construction8.reading_clear_iff
#print axioms Construction8.lap_and_phase
