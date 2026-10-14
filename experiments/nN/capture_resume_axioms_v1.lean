import LonelyRunner.LRC.Spec.CascadeGridN
import LonelyRunner.LRC.Spec.CascadeTransportN

-- Targeted audit of the resumed proof work; not a replacement for the full Spec gate.
#print axioms LRC.TwoBlock.exists_in_assigned_blocks
#print axioms LRC.RegimeSkeleton.gridStep8_two_bounded
#print axioms LRC.RegimeSkeleton.lonelyRunnerAt8_of_cover8
#print axioms LRC.CascadeTransport.move_eq_opening_of_only_blocker
#print axioms LRC.CascadeTransport.blocker_ne_setter
#print axioms LRC.CascadeTransport.reading_at_exit
#print axioms LRC.CascadeTransport.active_return_lap_increases
#print axioms LRC.CascadeTransport.return_lap_increases
#print axioms LRC.CascadeGrid.iterates_bounded_of_gridStep8_two
#print axioms LRC.CascadeGrid.fixed_of_gridStep8_two
