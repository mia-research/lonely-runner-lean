import Fresh.NativeUniformOpeningCells
import Fresh.NativeSeedResidueProduct
import Fresh.NativeMixedObserverGridSeeds
import Fresh.NativeFourUpperGrid
import Fresh.NativeArbitraryFourthGrid
import Fresh.NativeSmallFourthGrid
import Fresh.NativeComparableFourthGrid
import Fresh.NativeHierarchicalFourthGrid
import Fresh.NativeHierarchicalFourthArrangement
import Fresh.NativeRecoveredSecondGrid
import Fresh.NativeFourthReversalArrangement
import Fresh.NativeUpperTripleArrangement
import Fresh.NativePhaseOriginArrangement
import Fresh.NativeTightReboundCore
import Fresh.NativeUpperPairArrangement
import Fresh.NativeUpperGridHeightTransport
import Fresh.NativeUpperGridArrangement
import Fresh.NativeDoubleGridArrangement
import Fresh.NativeReturnedGridArrangement
import Fresh.NativeClearReboundArrangement
import Fresh.NativeClearWitnessArrangement
import Fresh.NativeReversalBranchArrangement
import Fresh.NativeSuppliedReversalArrangement
import Fresh.NativeCapturedReversalFamily
import Fresh.NativeArbitraryThirdReversal
import Fresh.NativeReversalCellEnvelope
import Fresh.NativeQuietReversalFamily
import Fresh.NativeOpeningLabelReversal
import Fresh.NativeLabelBoundaryFrontiers
import Fresh.NativeMixedGroupTransport
import Fresh.NativeNarrowCaptureBlock
import Fresh.NativeWitnessPacketReentry
import Fresh.NativePacketExtremeRecovery
import Fresh.NativeRecapturedLabelReset
import Fresh.NativeCurrentLabelPacket
import Fresh.NativePacketHistoryCoalescence
import Fresh.NativeRecoveredHandoffBands
import Fresh.FourBlockRecoveryHandoffs
import Fresh.NativeFinalHandoffBands
import Fresh.FourBlockArrangementJoins
import Fresh.ThreeBlockNeighbourJoins
import Fresh.ThreeGapPacketJoins
import Fresh.FourPairStepIndependentJoins
import Fresh.FourAPPairsNativeClass
import Fresh.TrainFlankPacketJoins
import Fresh.FourPairPolynomialGaps
import Fresh.ThreeBlockEndpointSingleton
import Fresh.TwoSixNine
import Fresh.TwoSixThin
import Fresh.TrainFlankMiddlePartitionJoins
import Fresh.TrainFlankReverseMiddlePartitionJoins
import Fresh.ThreeBlockPartitionBypassClass
import Fresh.ProvedTypesR
import Fresh.TwoAPSeparated21
import Fresh.MiddleStepFiveArrangementAll
import Fresh.FullThreeFiveArrangement
import Fresh.MiddleStepFiveArrangement
import Fresh.FarTwoAPArrangementAll
import Fresh.UniformStepFourArrangementAll
import Fresh.MixedStepFourArrangement
import Fresh.MixedStepFourParamArrangement
import Fresh.MixedStepFourLowerArrangement
import Fresh.UnequalAPArrangement
import Fresh.ArrangementFamilyJoinsOct26
import Fresh.APCoreOpening
import Fresh.SplitAPReadingsClass
import Fresh.SignedAPReadingsClass
import Fresh.GeneralTwoAPArrangement
import Fresh.TrainFlankInterplay
import Fresh.TwoMoverSubjectClass
import Fresh.SplitAPArrangementAll

/-! Arrangement reductions established in the 2026-10-26 autonomous run.
The earlier classes remain unchanged. This union incorporates genuine input
families, including unbounded AP offsets and independently perturbed compact
blocks. It does not assert that the remaining arrangements form a finite list.
[PROVISIONAL: counting tool] inherited reference-opening/grid selections.
[PROVISIONAL: covering] inherited finite AP-parameter splits and S2 branches.
-/
namespace Fresh.ArrangementTypesOct26
open Fresh Fresh.ProvedTypesR Fresh.ProvedTypesScale

-- STANDING: DEFINITION
def FourByFourMixedClass (v : Fin 8 → ℝ) : Prop :=
  Fresh.MixedStepFourArrangement.MixedFourTwoArrangementClass v ∨
  Fresh.MixedStepFourParamArrangement.MixedFourParamArrangementClass v ∨
  Fresh.MixedStepFourLowerArrangement.MixedFourLowerArrangementClass v ∨
  Fresh.UniformStepFourArrangement.UniformFourArrangementClass v

theorem fourByFourMixed_isolation {v : Fin 8 → ℝ}
    (h : FourByFourMixedClass v) (k : Fin 8) : Isolation v k := by
  rcases h with h | h | h | h
  · exact Fresh.MixedStepFourArrangement.mixedFourTwoArrangement_isolation h k
  · exact Fresh.MixedStepFourParamArrangement.mixedFourParamArrangement_isolation h k
  · exact Fresh.MixedStepFourLowerArrangement.mixedFourLowerArrangement_isolation h k
  · exact Fresh.UniformStepFourArrangement.uniformFourArrangement_isolation h k

-- STANDING: DEFINITION
def ThreeByFiveClass (v : Fin 8 → ℝ) : Prop :=
  Fresh.MiddleStepFiveArrangementAll.MiddleFiveAllArrangementClass v ∨
  Fresh.FullThreeFiveArrangement.FullThreeFiveArrangementClass v

theorem threeByFive_isolation {v : Fin 8 → ℝ} (h : ThreeByFiveClass v)
    (k : Fin 8) : Isolation v k := by
  rcases h with h | h
  · exact Fresh.MiddleStepFiveArrangementAll.middleFiveAllArrangement_isolation h k
  · exact Fresh.FullThreeFiveArrangement.fullThreeFiveArrangement_isolation h k

-- STANDING: DEFINITION
def NewTypes (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  Fresh.APCoreOpening.APCoreOpeningClass v k ∨
  Fresh.SplitAPBands.SplitAPReadingsClass v k ∨
  Fresh.SplitAPBands.SignedAPReadingsClass v k ∨
  Fresh.SplitAPArrangement.GeneralTwoAPBlockClass v ∨
  Fresh.TrainFlankPair.PairTrainOpeningClass v k ∨
  Fresh.TrainFlank.TwoSlowTrainClass v k ∨
  Fresh.UnequalAPArrangement.UnequalTwoAPBlockClass v ∨
  FourByFourMixedClass v ∨
  ThreeByFiveClass v ∨
  Fresh.TwoAPSeparated21.SeparatedTwoAP21Class v ∨
  Fresh.TwoSixNine.TwoSixNineClass v ∨
  Fresh.TwoSixThin.TwoSixThinClass v ∨
  Fresh.FourBlockDoubleSingletonArrangement.DoubleCoveredClass v ∨
  Fresh.ThreeBlockReverseMiddlePartitions.ThreeBlockReverseMiddlePartitionsClass v ∨
  Fresh.ThreeGapPacketBand.ThreeGapPacketClass v k ∨
  Fresh.FourAPPairsNativeClass.FourPairNativeClass v k ∨
  Fresh.FourBlockNeighbour.FourBlockInternalClass v k ∨
  Fresh.ThreeBlockPartitionBypassClass.PartitionNativeBypassClass v k ∨
  Fresh.FourPairStepIndependentPhysical.FourPairStepIndependentClass v k ∨
  Fresh.OneMover.TwoMoverSubjectClass v ∨
  Fresh.NativeCanonicalReturn.CanonicalReturnClass v k

theorem newTypes_isolation {v : Fin 8 → ℝ} {k : Fin 8}
    (h : NewTypes v k) : Isolation v k := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact Fresh.APCoreOpening.apCoreOpening_isolation h
  · exact Fresh.SplitAPBands.splitAPReadings_isolation h
  · exact Fresh.SplitAPBands.signedAPReadings_isolation h
  · exact Fresh.SplitAPArrangement.generalTwoAPBlock_isolation h k
  · exact Fresh.TrainFlankPair.pairTrainOpening_isolation h
  · exact Fresh.TrainFlank.twoSlowTrain_isolation h
  · exact Fresh.UnequalAPArrangement.unequalTwoAPBlock_isolation h k
  · exact fourByFourMixed_isolation h k
  · exact threeByFive_isolation h k
  · exact Fresh.TwoAPSeparated21.separatedTwoAP21_isolation h k
  · exact Fresh.TwoSixNine.twoSixNine_isolation h k
  · exact Fresh.TwoSixThin.twoSixThin_isolation h k
  · exact Fresh.FourBlockDoubleSingletonArrangement.doubleCovered_isolation h k
  · exact Fresh.ThreeBlockReverseMiddlePartitions.threeBlockReverseMiddlePartitions_isolation h k
  · exact Fresh.ThreeGapPacketBand.threeGapPacket_isolation h
  · exact Fresh.FourAPPairsNativeClass.fourPairNative_isolation h
  · exact Fresh.FourBlockNeighbour.fourBlockInternal_isolation h
  · exact Fresh.ThreeBlockPartitionBypassClass.partitionNativeBypass_isolation h
  · exact Fresh.FourPairStepIndependentPhysical.fourPairStepIndependent_isolation h
  · exact Fresh.OneMover.twoMoverSubjectClass_isolation h k
  · exact Fresh.NativeCanonicalReturn.canonical_isolation h

-- STANDING: DEFINITION
def Types (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  TypesProvedRUp v k ∨ NewTypes v k

theorem types_isolation {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v)
    {k : Fin 8} (h : Types v k) : Isolation v k := by
  rcases h with h | h
  · exact typesProvedRUp_isolation hv h
  · exact newTypes_isolation h

-- STANDING: DEFINITION
def TypesUp (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ c : ℝ, 0 < c ∧ Types (fun j => c*v j) k

-- STANDING: DEFINITION
def ReducedAdmissible (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsOrderedArrangement v ∧ ¬ TypesUp v k

theorem typesUp_isolation {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v)
    {k : Fin 8} (h : TypesUp v k) : Isolation v k := by
  obtain ⟨c,hc,h⟩ := h
  exact (Isolation_smul hc).1 (types_isolation (orderedArrangement_smul hc hv) h)

theorem typesUp_or_reduced {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v)
    (k : Fin 8) : TypesUp v k ∨ ReducedAdmissible v k := by
  by_cases h : TypesUp v k
  · exact Or.inl h
  · exact Or.inr ⟨hv,h⟩

theorem types_imp_up {v : Fin 8 → ℝ} {k : Fin 8} (h : Types v k) : TypesUp v k := by
  refine ⟨1,by norm_num,?_⟩
  simpa using h

theorem reduced_imp_old_admissible {v : Fin 8 → ℝ} {k : Fin 8}
    (h : ReducedAdmissible v k) : AdmissibleRUp v k := by
  refine ⟨h.1,fun hold => h.2 (types_imp_up (Or.inl hold))⟩

theorem reduced_excludes_new {v : Fin 8 → ℝ} {k : Fin 8}
    (h : ReducedAdmissible v k) : ¬ NewTypes v k := by
  intro hnew
  exact h.2 (types_imp_up (Or.inr hnew))

theorem typesUp_smul {c : ℝ} (hc : 0 < c) {v : Fin 8 → ℝ} {k : Fin 8} :
    TypesUp (fun j => c*v j) k ↔ TypesUp v k := by
  constructor
  · rintro ⟨b,hb,h⟩
    refine ⟨b*c,by positivity,?_⟩
    have he : (fun j => b*(c*v j)) = (fun j => (b*c)*v j) := by funext j; ring
    rwa [he] at h
  · rintro ⟨b,hb,h⟩
    refine ⟨b/c,by positivity,?_⟩
    have he : (fun j => b/c*(c*v j)) = (fun j => b*v j) := by funext j; field_simp
    rwa [he]

theorem shortAnchor_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.FourBlockShortAnchorArrangement.ShortAnchorClass v) : NewTypes v k := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Fresh.FourBlockShortAnchorArrangement.shortAnchor_into_shortOpening h))))))))))))))))

theorem openingRecovery_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.FourBlockOpeningRecoveryArrangement.RecoveryClass v) : NewTypes v k := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Fresh.FourBlockOpeningRecoveryArrangement.recovery_into_leftCharts h)))))))))))))))))

theorem middlePacket_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.FourBlockMiddlePacketArrangement.MiddlePacketClass v) : NewTypes v k := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr h))))))))))))))

theorem doubleSingleton_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.FourBlockDoubleSingletonArrangement.DoubleSingletonClass v) : NewTypes v k := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr h)))))))))))))

theorem middleEntry_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.FourBlockPacketEntryArrangement.MiddleEntryClass v) : NewTypes v k :=
  middlePacket_into_newTypes k (Fresh.FourBlockPacketEntryArrangement.middleEntry_into_middle h)

theorem doubleEntry_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.FourBlockPacketEntryArrangement.DoubleEntryClass v) : NewTypes v k :=
  doubleSingleton_into_newTypes k (Fresh.FourBlockPacketEntryArrangement.doubleEntry_into_double h)

theorem fourBlock_reversed_newTypes_isolation (c g h j : ℝ) (p q r s : ℕ)
    (hs : p+q+r+s=8) (k : Fin 8)
    (hinput : NewTypes (Fresh.FourBlockNeighbour.speeds c j h g s r q) (Fresh.FourBlockReversal.rev k)) :
    Isolation (Fresh.FourBlockNeighbour.speeds c g h j p q r) k := by
  have hi := (Fresh.FourBlockReversal.isolation_reversal c g h j p q r s hs (Fresh.FourBlockReversal.rev k)).1
    (newTypes_isolation hinput)
  simpa only [Fresh.FourBlockReversal.rev_rev] using hi

theorem canonicalReturn_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeCanonicalReturn.CanonicalReturnClass v k) : NewTypes v k := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))))))))))))))))

theorem noReturn_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeCanonicalReturn.NoReturnClass v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeCanonicalReturn.noReturn_into_canonical h)

theorem sharpReturn_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReturnCapture.SharpReturnClass v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeCanonicalReturn.sharp_into_canonical h)

#print axioms canonicalReturn_into_newTypes
#print axioms noReturn_into_newTypes
theorem zeroReturn_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReturnCapture.ZeroReturnClass v k) : NewTypes v k :=
  sharpReturn_into_newTypes k (Fresh.NativeReturnCapture.zero_into_sharp h)

theorem quarterReturn_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReturnCapture.QuarterReturnClass v k) : NewTypes v k :=
  sharpReturn_into_newTypes k (Fresh.NativeReturnCapture.quarter_into_sharp h)

theorem quarterZeroReturn_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReturnJoins.QuarterZeroReturnClass v k) : NewTypes v k :=
  quarterReturn_into_newTypes k (Fresh.NativeReturnJoins.quarterZero_into_quarter h)

theorem relativeCapture_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeRelativeCapture.RelativeCaptureClass v k) : NewTypes v k :=
  sharpReturn_into_newTypes k (Fresh.NativeReturnJoins.relative_into_sharp h)

theorem fastestRecovery_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.FastestCaptureRecovery.FastestRecoveryClass v k) : NewTypes v k :=
  relativeCapture_into_newTypes k (Fresh.NativeRelativeCapture.fastest_into_relative h)

theorem fastestCapture_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.FastestCaptureRetention.FastestCaptureClass v k) : NewTypes v k :=
  fastestRecovery_into_newTypes k (Fresh.FastestCaptureRecovery.retained_into_recovery h)

theorem actualFastest_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.FastestCaptureRecovery.ActualFastestClass v k) : NewTypes v k :=
  fastestRecovery_into_newTypes k (Fresh.FastestCaptureRecovery.actual_into_recovery h)

#print axioms sharpReturn_into_newTypes
#print axioms zeroReturn_into_newTypes
#print axioms quarterReturn_into_newTypes
#print axioms quarterZeroReturn_into_newTypes
#print axioms relativeCapture_into_newTypes
#print axioms fastestRecovery_into_newTypes
#print axioms actualFastest_into_newTypes
#print axioms fastestCapture_into_newTypes
#print axioms middleEntry_into_newTypes
#print axioms doubleEntry_into_newTypes
#print axioms fourBlock_reversed_newTypes_isolation
#print axioms doubleSingleton_into_newTypes
#print axioms middlePacket_into_newTypes
#print axioms shortAnchor_into_newTypes
#print axioms openingRecovery_into_newTypes
#print axioms fourByFourMixed_isolation
#print axioms threeByFive_isolation
#print axioms newTypes_isolation
#print axioms types_isolation
#print axioms typesUp_isolation
#print axioms typesUp_or_reduced
#print axioms types_imp_up
#print axioms reduced_imp_old_admissible
#print axioms reduced_excludes_new
#print axioms typesUp_smul
theorem handoffNoReturn_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReturnHandoffArrangement.HandoffNoReturnClass v k) : NewTypes v k :=
  noReturn_into_newTypes k (Fresh.NativeReturnHandoffArrangement.handoff_into_noReturn h)

#print axioms handoffNoReturn_into_newTypes

theorem handoffRecovered_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReturnHandoffArrangement.HandoffRecoveredClass v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeReturnHandoffArrangement.handoff_into_canonical h)

#print axioms handoffRecovered_into_newTypes

theorem soleNoReturn_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReturnHandoffArrangement.SoleNoReturnClass v k) : NewTypes v k :=
  handoffNoReturn_into_newTypes k (Fresh.NativeReturnHandoffArrangement.sole_noReturn_into_handoff h)

#print axioms soleNoReturn_into_newTypes

theorem soleRecovered_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReturnHandoffArrangement.SoleRecoveredClass v k) : NewTypes v k :=
  handoffRecovered_into_newTypes k (Fresh.NativeReturnHandoffArrangement.sole_recovered_into_handoff h)

#print axioms soleRecovered_into_newTypes

theorem handoffRelative_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReturnHandoffArrangement.HandoffRelativeClass v k) : NewTypes v k :=
  handoffNoReturn_into_newTypes k (Fresh.NativeReturnHandoffArrangement.relative_into_noReturn_handoff h)

#print axioms handoffRelative_into_newTypes

theorem soleRelative_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReturnHandoffArrangement.SoleRelativeClass v k) : NewTypes v k :=
  handoffRelative_into_newTypes k (Fresh.NativeReturnHandoffArrangement.sole_relative_into_handoff h)

#print axioms soleRelative_into_newTypes

theorem handoffQuarter_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReturnHandoffArrangement.HandoffQuarterClass v k) : NewTypes v k :=
  handoffNoReturn_into_newTypes k (Fresh.NativeReturnHandoffArrangement.quarter_into_noReturn_handoff h)

#print axioms handoffQuarter_into_newTypes

theorem soleQuarter_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReturnHandoffArrangement.SoleQuarterClass v k) : NewTypes v k :=
  handoffQuarter_into_newTypes k (Fresh.NativeReturnHandoffArrangement.sole_quarter_into_handoff h)

#print axioms soleQuarter_into_newTypes

theorem handoffSharp_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeHandoffEntryFaces.HandoffSharpClass v k) : NewTypes v k :=
  handoffNoReturn_into_newTypes k (Fresh.NativeHandoffEntryFaces.sharp_into_noReturn h)

#print axioms handoffSharp_into_newTypes

theorem soleSharp_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeHandoffEntryFaces.SoleSharpClass v k) : NewTypes v k :=
  handoffSharp_into_newTypes k (Fresh.NativeHandoffEntryFaces.sole_sharp_into_handoff h)

#print axioms soleSharp_into_newTypes

theorem selfClosing_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReturnClosingOrder.SelfClosingClass v k) : NewTypes v k :=
  handoffNoReturn_into_newTypes k (Fresh.NativeReturnClosingOrder.selfClosing_into_noReturn h)

#print axioms selfClosing_into_newTypes

theorem soleSelfClosing_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReturnClosingOrder.SoleSelfClosingClass v k) : NewTypes v k :=
  selfClosing_into_newTypes k (Fresh.NativeReturnClosingOrder.soleSelfClosing_into_selfClosing h)

#print axioms soleSelfClosing_into_newTypes

theorem returnGroupReset_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReturnGroupArrangement.ResetClass v k) : NewTypes v k :=
  handoffNoReturn_into_newTypes k (Fresh.NativeReturnGroupArrangement.reset_into_noReturn h)

#print axioms returnGroupReset_into_newTypes

theorem returnGroupCompact_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReturnGroupArrangement.CompactClass v k) : NewTypes v k :=
  returnGroupReset_into_newTypes k (Fresh.NativeReturnGroupArrangement.compact_into_reset_class h)

#print axioms returnGroupCompact_into_newTypes

theorem returnGroupCommon_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReturnGroupArrangement.CommonClass v k) : NewTypes v k :=
  returnGroupCompact_into_newTypes k (Fresh.NativeReturnGroupArrangement.common_into_compact_class h)

#print axioms returnGroupCommon_into_newTypes

theorem returnGroupAnchor_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReturnGroupArrangement.AnchorClass v k) : NewTypes v k :=
  returnGroupCompact_into_newTypes k (Fresh.NativeReturnGroupArrangement.anchor_into_compact_class h)

#print axioms returnGroupAnchor_into_newTypes

theorem singleReturnRelay_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeSingleReturnArrangement.RelayClass v k) : NewTypes v k :=
  returnGroupCompact_into_newTypes k (Fresh.NativeReturnGroupArrangement.single_into_compact_class h)

#print axioms singleReturnRelay_into_newTypes

theorem singleReturnAnchor_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeSingleReturnArrangement.AnchorClass v k) : NewTypes v k :=
  singleReturnRelay_into_newTypes k (Fresh.NativeSingleReturnArrangement.anchor_into_relay h)

#print axioms singleReturnAnchor_into_newTypes

theorem singleReturnRecovery_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeSingleReturnArrangement.RecoveryClass v k) : NewTypes v k :=
  handoffRecovered_into_newTypes k (Fresh.NativeSingleReturnArrangement.recovery_into_recovered h)

#print axioms singleReturnRecovery_into_newTypes

theorem returnFaceRelay_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReturnFaceHandoff.FaceRelayClass v k) : NewTypes v k :=
  singleReturnRelay_into_newTypes k (Fresh.NativeReturnFaceHandoff.face_into_single_relay_class h)

#print axioms returnFaceRelay_into_newTypes

theorem returnGroupSharp_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReturnGroupFaces.SharpClass v k) : NewTypes v k :=
  returnGroupReset_into_newTypes k (Fresh.NativeReturnGroupFaces.sharp_into_reset_class h)

#print axioms returnGroupSharp_into_newTypes

theorem returnGroupQuarter_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReturnGroupFaces.QuarterClass v k) : NewTypes v k :=
  returnGroupSharp_into_newTypes k (Fresh.NativeReturnGroupFaces.quarter_into_sharp_class h)

#print axioms returnGroupQuarter_into_newTypes

theorem repeatedRecovery_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeRepeatedReturnArrangement.RecoveryClass v k) : NewTypes v k :=
  singleReturnRecovery_into_newTypes k (Fresh.NativeRepeatedReturnArrangement.recovery_into_single h)

#print axioms repeatedRecovery_into_newTypes

theorem repeatedRelay_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeRepeatedReturnArrangement.RelayClass v k) : NewTypes v k :=
  singleReturnRelay_into_newTypes k (Fresh.NativeRepeatedReturnArrangement.relay_into_single h)

#print axioms repeatedRelay_into_newTypes

theorem repeatedRecoveredRelay_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeRepeatedReturnArrangement.RecoveredRelayClass v k) : NewTypes v k :=
  handoffRecovered_into_newTypes k (Fresh.NativeRepeatedReturnArrangement.recoveredRelay_into_handoff h)

#print axioms repeatedRecoveredRelay_into_newTypes

theorem excursionRecovery_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeExcursionArrangement.RecoveryClass v k) : NewTypes v k :=
  handoffRecovered_into_newTypes k (Fresh.NativeExcursionArrangement.recovery_into_recovered h)

#print axioms excursionRecovery_into_newTypes

theorem excursionRelay_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeExcursionArrangement.RelayClass v k) : NewTypes v k :=
  handoffRelative_into_newTypes k (Fresh.NativeExcursionArrangement.relay_into_relative h)

#print axioms excursionRelay_into_newTypes

theorem residualRelay_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeExcursionOpeningOrder.RelayClass v k) : NewTypes v k :=
  handoffRelative_into_newTypes k (Fresh.NativeExcursionOpeningOrder.relay_into_relative h)

#print axioms residualRelay_into_newTypes

theorem frontierQuarter_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeSurvivorDominance.FrontierQuarterClass v k) : NewTypes v k :=
  handoffQuarter_into_newTypes k (Fresh.NativeSurvivorDominance.frontier_into_quarter h)

#print axioms frontierQuarter_into_newTypes

theorem capturedPartner_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeCapturedPartnerJoin.PartnerClass v k) : NewTypes v k :=
  noReturn_into_newTypes k (Fresh.NativeCapturedPartnerJoin.partner_into_noReturn h)

#print axioms capturedPartner_into_newTypes

theorem compactPartner_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeCapturedPartnerJoin.CompactClass v k) : NewTypes v k :=
  capturedPartner_into_newTypes k (Fresh.NativeCapturedPartnerJoin.compact_into_partner h)

#print axioms compactPartner_into_newTypes

theorem openingCohort_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeCapturedPartnerJoin.CohortClass v k) : NewTypes v k :=
  capturedPartner_into_newTypes k (Fresh.NativeCapturedPartnerJoin.cohort_into_partner h)

#print axioms openingCohort_into_newTypes

theorem gridCohort_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeCapturedPartnerJoin.GridCohortClass v k) : NewTypes v k :=
  openingCohort_into_newTypes k (Fresh.NativeCapturedPartnerJoin.grid_into_cohort h)

#print axioms gridCohort_into_newTypes

theorem openingFace_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeCapturedPartnerJoin.FaceClass v k) : NewTypes v k :=
  capturedPartner_into_newTypes k (Fresh.NativeCapturedPartnerJoin.face_into_partner h)

#print axioms openingFace_into_newTypes

theorem recoveredCohort_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeCohortReturns.RecoveredCohortClass v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeCohortReturns.recovered_into_canonical h)

#print axioms recoveredCohort_into_newTypes

theorem outsiderPartner_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeCohortOutsiderRelay.OutsiderPartnerClass v k) : NewTypes v k :=
  capturedPartner_into_newTypes k (Fresh.NativeCohortOutsiderRelay.outsiderPartner_into_partner h)

#print axioms outsiderPartner_into_newTypes

theorem outsiderRecovery_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeCohortOutsiderRelay.OutsiderRecoveryClass v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeCohortOutsiderRelay.outsiderRecovery_into_canonical h)

#print axioms outsiderRecovery_into_newTypes

theorem cohortReturnPartner_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeCohortReturnOrder.ReturnPartnerClass v k) : NewTypes v k :=
  capturedPartner_into_newTypes k (Fresh.NativeCohortReturnOrder.returnPartner_into_partner h)

#print axioms cohortReturnPartner_into_newTypes

theorem cohortReturnRecovery_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeCohortReturnOrder.ReturnRecoveryClass v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeCohortReturnOrder.returnRecovery_into_canonical h)

#print axioms cohortReturnRecovery_into_newTypes

theorem cohortReturnFrontier_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeCohortReturnOrder.FrontierRetainedClass v k) : NewTypes v k :=
  noReturn_into_newTypes k (Fresh.NativeCohortReturnOrder.frontierRetained_into_noReturn h)

#print axioms cohortReturnFrontier_into_newTypes

theorem homogeneousReturn_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeSelectedLevelClearance.HomogeneousRetainedClass v k) : NewTypes v k :=
  noReturn_into_newTypes k (Fresh.NativeSelectedLevelClearance.homogeneousRetained_into_noReturn h)

#print axioms homogeneousReturn_into_newTypes

theorem returnLevelRecovery_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReturnLevelClearance.LevelRecoveryClass v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeReturnLevelClearance.levelRecovery_into_canonical h)

#print axioms returnLevelRecovery_into_newTypes

theorem returnPhaseRecovery_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReturnLevelClearance.PhaseRecoveryClass v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeReturnLevelClearance.phaseRecovery_into_canonical h)

#print axioms returnPhaseRecovery_into_newTypes

theorem maxReturnLevel_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeOrderedReturnLevels.MaxLevelRetainedClass v k) : NewTypes v k :=
  noReturn_into_newTypes k (Fresh.NativeOrderedReturnLevels.maxLevel_into_noReturn h)

#print axioms maxReturnLevel_into_newTypes

theorem orderedReturnRecovery_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeOrderedReturnLevels.OrderedRecoveryClass v k) : NewTypes v k :=
  returnLevelRecovery_into_newTypes k (Fresh.NativeOrderedReturnLevels.orderedRecovery_into_level h)

#print axioms orderedReturnRecovery_into_newTypes

theorem generalReturnPhase_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeOrderedReturnLevels.GeneralPhaseRecoveryClass v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeOrderedReturnLevels.generalPhase_into_canonical h)

#print axioms generalReturnPhase_into_newTypes

theorem twoSetterPacket_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeTwoSetterPacket.TwoSetterPartnerClass v k) : NewTypes v k :=
  capturedPartner_into_newTypes k (Fresh.NativeTwoSetterPacket.twoSetter_into_partner h)

#print axioms twoSetterPacket_into_newTypes

theorem doubleHighRecovery_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeTwoSetterPacket.DoubleHighRecoveryClass v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeTwoSetterPacket.doubleHigh_into_canonical h)

#print axioms doubleHighRecovery_into_newTypes

theorem cohortPhaseRecovery_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeTwoSetterPacket.CohortPhaseRecoveryClass v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeTwoSetterPacket.cohortPhase_into_canonical h)

#print axioms cohortPhaseRecovery_into_newTypes

theorem oneReaderDeformation_actual_move {v w : Fin 8 → ℝ}
    (hw : IsArrangement w) (k a : Fin 8) (ha : a≠k)
    (he : ∀ i : Fin 8,i≠a → w i=v i) (U : ℝ) :
    IsMove (disparitySet w k) U
      (max (Fresh.Cascade.step (Fresh.NativeOneReaderDeformation.others v k a) U)
        (Fresh.NativeOneReaderDeformation.labelledOpening (Fresh.NativeReturnHandoff.reading w k a) U)) := by
  rw [←Fresh.NativeOneReaderDeformation.physical_deformation_step hw k a ha he U]
  exact Fresh.Cascade.isMove_step _ _

#print axioms oneReaderDeformation_actual_move

theorem coalescedSoleFits_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeCoalescedCaptureArrangement.SoleFitsClass v k) : NewTypes v k :=
  capturedPartner_into_newTypes k (Fresh.NativeCoalescedCaptureArrangement.soleFits_into_partner h)

#print axioms coalescedSoleFits_into_newTypes

theorem delayedRejoinInterval_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeCoalescedCaptureArrangement.RejoinIntervalClass v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeCoalescedCaptureArrangement.rejoinInterval_into_canonical h)

#print axioms delayedRejoinInterval_into_newTypes

theorem fixedPrefixRecovery_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeFixedPrefixArrangement.PrefixRecoveryClass v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeFixedPrefixArrangement.prefixRecovery_into_canonical h)

#print axioms fixedPrefixRecovery_into_newTypes

theorem fixedPrefixClosing_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeFixedPrefixArrangement.ClosingGuardClass v k) : NewTypes v k :=
  fixedPrefixRecovery_into_newTypes k (Fresh.NativeFixedPrefixArrangement.closingGuard_into_prefixRecovery h)

#print axioms fixedPrefixClosing_into_newTypes

theorem retainedTailInterval_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeFixedPrefixArrangement.TailIntervalClass v k) : NewTypes v k :=
  fixedPrefixRecovery_into_newTypes k (Fresh.NativeFixedPrefixArrangement.tailInterval_into_prefixRecovery h)

#print axioms retainedTailInterval_into_newTypes

theorem terminalTailInterval_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeFixedPrefixArrangement.TerminalIntervalClass v k) : NewTypes v k :=
  capturedPartner_into_newTypes k (Fresh.NativeFixedPrefixArrangement.terminalInterval_into_partner h)

#print axioms terminalTailInterval_into_newTypes

theorem groupEndpointRecovery_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeGroupEndpointRecovery.GroupEndpointClass v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeGroupEndpointRecovery.groupEndpoint_into_canonical h)

#print axioms groupEndpointRecovery_into_newTypes

theorem packetRestartExchange_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativePacketRestartExchange.ExchangeEndpointClass v k) : NewTypes v k :=
  groupEndpointRecovery_into_newTypes k (Fresh.NativePacketRestartExchange.exchangeEndpoint_into_groupEndpoint h)

#print axioms packetRestartExchange_into_newTypes

theorem openingPairRecovery_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeOpeningReversalArrangement.PairRecoveryClass v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeOpeningReversalArrangement.pairRecovery_into_canonical h)

#print axioms openingPairRecovery_into_newTypes

theorem openingPairGuard_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeOpeningReversalArrangement.PairGuardClass v k) : NewTypes v k :=
  openingPairRecovery_into_newTypes k (Fresh.NativeOpeningReversalArrangement.pairGuard_into_recovery h)

#print axioms openingPairGuard_into_newTypes

theorem thirdReaderRecovery_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeThirdReaderArrangement.TripleRecoveryClass v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeThirdReaderArrangement.tripleRecovery_into_canonical h)

#print axioms thirdReaderRecovery_into_newTypes

theorem thirdReaderSimple_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeThirdReaderArrangement.SimpleTripleClass v k) : NewTypes v k :=
  thirdReaderRecovery_into_newTypes k (Fresh.NativeThirdReaderArrangement.simpleTriple_into_recovery h)

#print axioms thirdReaderSimple_into_newTypes

theorem thirdReaderGuard_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeThirdReaderArrangement.TripleGuardClass v k) : NewTypes v k :=
  thirdReaderRecovery_into_newTypes k (Fresh.NativeThirdReaderArrangement.tripleGuard_into_recovery h)

#print axioms thirdReaderGuard_into_newTypes

theorem forcedThirdReader_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeThirdReaderForcedArrangement.ForcedTripleClass v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeThirdReaderForcedArrangement.forcedTriple_into_canonical h)

#print axioms forcedThirdReader_into_newTypes

theorem forcedThirdReaderGuard_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeThirdReaderForcedArrangement.ForcedTripleGuardClass v k) : NewTypes v k :=
  forcedThirdReader_into_newTypes k (Fresh.NativeThirdReaderForcedArrangement.forcedTripleGuard_into_forced h)

#print axioms forcedThirdReaderGuard_into_newTypes

theorem residualPhaseRecovery_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeResidualReturnArrangement.ResidualRecoveryClass v k) : NewTypes v k :=
  openingPairRecovery_into_newTypes k (Fresh.NativeResidualReturnArrangement.residualRecovery_into_pair h)

#print axioms residualPhaseRecovery_into_newTypes

theorem residualPhaseGuard_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeResidualReturnArrangement.ResidualGuardClass v k) : NewTypes v k :=
  residualPhaseRecovery_into_newTypes k (Fresh.NativeResidualReturnArrangement.residualGuard_into_recovery h)

#print axioms residualPhaseGuard_into_newTypes

theorem residualPhaseCompact_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeResidualReturnArrangement.ResidualCompactClass v k) : NewTypes v k :=
  residualPhaseRecovery_into_newTypes k (Fresh.NativeResidualReturnArrangement.residualCompact_into_recovery h)

#print axioms residualPhaseCompact_into_newTypes

theorem residualPhaseEarly_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeResidualReturnArrangement.ResidualEarlyClass v k) : NewTypes v k :=
  residualPhaseRecovery_into_newTypes k (Fresh.NativeResidualReturnArrangement.residualEarly_into_recovery h)

#print axioms residualPhaseEarly_into_newTypes

theorem residualPhaseBand_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeResidualReturnArrangement.ResidualBandClass v k) : NewTypes v k :=
  residualPhaseRecovery_into_newTypes k (Fresh.NativeResidualReturnArrangement.residualBand_into_recovery h)

#print axioms residualPhaseBand_into_newTypes

theorem residualSoleClosing_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeResidualReturnArrangement.ResidualSoleClosingClass v k) : NewTypes v k :=
  soleSharp_into_newTypes k (Fresh.NativeResidualReturnArrangement.residualSoleClosing_into_soleSharp h)

#print axioms residualSoleClosing_into_newTypes

theorem residualInverseTriple_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeResidualReturnArrangement.ResidualInverseTripleClass v k) : NewTypes v k :=
  forcedThirdReader_into_newTypes k (Fresh.NativeResidualReturnArrangement.residualInverse_into_forcedTriple h)

#print axioms residualInverseTriple_into_newTypes

theorem outsidePacketRecovery_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeOutsideGroupArrangement.OutsideRecoveryClass v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeOutsideGroupArrangement.outsideRecovery_into_canonical h)

#print axioms outsidePacketRecovery_into_newTypes

theorem outsidePacketGuard_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeOutsideGroupArrangement.OutsideGuardClass v k) : NewTypes v k :=
  outsidePacketRecovery_into_newTypes k (Fresh.NativeOutsideGroupArrangement.outsideGuard_into_recovery h)

#print axioms outsidePacketGuard_into_newTypes

theorem allOutsideCaptured_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeOutsideGroupArrangement.AllOutsideCapturedClass v k) : NewTypes v k :=
  outsidePacketGuard_into_newTypes k (Fresh.NativeOutsideGroupArrangement.allOutsideCaptured_into_guard h)

#print axioms allOutsideCaptured_into_newTypes

theorem independentOutsideBand_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeOutsideGroupArrangement.IndependentOutsideBandClass v k) : NewTypes v k :=
  allOutsideCaptured_into_newTypes k (Fresh.NativeOutsideGroupArrangement.independentBand_into_allCaptured h)

#print axioms independentOutsideBand_into_newTypes

theorem firstOutsideWatcher_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeOutsideGroupArrangement.FirstWatcherGuardClass v k) : NewTypes v k :=
  outsidePacketGuard_into_newTypes k (Fresh.NativeOutsideGroupArrangement.firstWatcher_into_guard h)

#print axioms firstOutsideWatcher_into_newTypes

theorem watcherPacketRecovery_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeWatcherReturnArrangement.RecoveryClass v k) : NewTypes v k :=
  residualPhaseCompact_into_newTypes k (Fresh.NativeWatcherReturnArrangement.recovery_into_residualCompact h)

#print axioms watcherPacketRecovery_into_newTypes

theorem watcherPacketGuard_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeWatcherReturnArrangement.GuardClass v k) : NewTypes v k :=
  watcherPacketRecovery_into_newTypes k (Fresh.NativeWatcherReturnArrangement.guard_into_recovery h)

#print axioms watcherPacketGuard_into_newTypes

theorem watcherMultiReturn_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeWatcherReturnArrangement.MultiReturnClass v k) : NewTypes v k :=
  watcherPacketRecovery_into_newTypes k (Fresh.NativeWatcherReturnArrangement.multiReturn_into_recovery h)

#print axioms watcherMultiReturn_into_newTypes

theorem watcherEarlyPhase_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeWatcherReturnArrangement.EarlyPhaseClass v k) : NewTypes v k :=
  watcherPacketRecovery_into_newTypes k (Fresh.NativeWatcherReturnArrangement.earlyPhase_into_recovery h)

#print axioms watcherEarlyPhase_into_newTypes

theorem watcherBoundaryRecovery_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeWatcherReturnArrangement.BoundaryRecoveryClass v k) : NewTypes v k :=
  residualPhaseCompact_into_newTypes k (Fresh.NativeWatcherReturnArrangement.boundaryRecovery_into_residualCompact h)

#print axioms watcherBoundaryRecovery_into_newTypes

theorem watcherBoundaryGuard_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeWatcherReturnArrangement.BoundaryGuardClass v k) : NewTypes v k :=
  watcherBoundaryRecovery_into_newTypes k (Fresh.NativeWatcherReturnArrangement.boundaryGuard_into_boundaryRecovery h)

#print axioms watcherBoundaryGuard_into_newTypes

theorem watcherFirstBoundary_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeWatcherReturnArrangement.FirstBoundaryGuardClass v k) : NewTypes v k :=
  watcherBoundaryGuard_into_newTypes k (Fresh.NativeWatcherReturnArrangement.firstBoundaryGuard_into_guard h)

#print axioms watcherFirstBoundary_into_newTypes

theorem retainedPacketTail_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativePacketTailArrangement.RecoveryClass v k) : NewTypes v k :=
  openingPairRecovery_into_newTypes k (Fresh.NativePacketTailArrangement.recovery_into_pair h)

#print axioms retainedPacketTail_into_newTypes

theorem twoPacketTailGuard_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativePacketTailArrangement.TwoPacketGuardClass v k) : NewTypes v k :=
  retainedPacketTail_into_newTypes k (Fresh.NativePacketTailArrangement.twoPacketGuard_into_recovery h)

#print axioms twoPacketTailGuard_into_newTypes

theorem postWatcherResetTail_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativePacketTailArrangement.PostResetClass v k) : NewTypes v k :=
  retainedPacketTail_into_newTypes k (Fresh.NativePacketTailArrangement.postReset_into_recovery h)

#print axioms postWatcherResetTail_into_newTypes

theorem recoveredPacketBox_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeRecoveredPacketBands.BoxClass v k) : NewTypes v k :=
  residualPhaseBand_into_newTypes k (Fresh.NativeRecoveredPacketBands.box_into_residualBand h)

#print axioms recoveredPacketBox_into_newTypes

theorem rebasedPacketChart_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeRebasedPacketChart.ChartClass v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeRebasedPacketChart.chart_into_canonical h)

#print axioms rebasedPacketChart_into_newTypes

theorem rebasedPacketChart_into_types {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeRebasedPacketChart.ChartClass v k) : Types v k := by
  have hu := Fresh.NativeRebasedPacketChart.chart_into_unblocked h
  have hb : Fresh.Admissible.Proved v k := Or.inr (Or.inr hu)
  have hp : Fresh.AdmissiblePlus.ProvedPlus v k := Or.inl hb
  have hf : Fresh.AdmissibleFlank.FlankProved v k := Or.inl hp
  have hm : Fresh.AdmissibleMore.MoreProved v k := Or.inl hf
  have ht : Fresh.ProvedTypes.TypesProved v k := Or.inl hm
  have hr : Fresh.ProvedTypesR.TypesProvedR v k := Or.inl ht
  exact Or.inl ⟨1,by norm_num,by simpa using hr⟩

#print axioms rebasedPacketChart_into_types

theorem rebasedPacketChart_not_reduced {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeRebasedPacketChart.ChartClass v k) : ¬ReducedAdmissible v k := by
  intro hr
  exact hr.2 (types_imp_up (rebasedPacketChart_into_types k h))

#print axioms rebasedPacketChart_not_reduced

theorem finalHandoffBands_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeFinalHandoffBands.BandClass v k) : NewTypes v k :=
  capturedPartner_into_newTypes k (Fresh.NativeFinalHandoffBands.band_into_partner h)

#print axioms finalHandoffBands_into_newTypes

theorem currentLabelRetained_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeCurrentLabelPacket.RetainedClass v k) : NewTypes v k :=
  capturedPartner_into_newTypes k (Fresh.NativeCurrentLabelPacket.retained_into_partner h)

#print axioms currentLabelRetained_into_newTypes

theorem currentLabelRecovered_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeCurrentLabelPacket.RecoveredClass v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeCurrentLabelPacket.recovered_into_canonical h)

#print axioms currentLabelRecovered_into_newTypes

theorem recoveredHandoffBands_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeRecoveredHandoffBands.BandClass v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeRecoveredHandoffBands.band_into_canonical h)

#print axioms recoveredHandoffBands_into_newTypes

theorem recapturedRetainedReset_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeRecapturedLabelReset.RetainedResetClass v k) : NewTypes v k :=
  currentLabelRetained_into_newTypes k (Fresh.NativeRecapturedLabelReset.retainedReset_into_current h)

#print axioms recapturedRetainedReset_into_newTypes

theorem recapturedRecoveredReset_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeRecapturedLabelReset.RecoveredResetClass v k) : NewTypes v k :=
  currentLabelRecovered_into_newTypes k (Fresh.NativeRecapturedLabelReset.recoveredReset_into_current h)

#print axioms recapturedRecoveredReset_into_newTypes

theorem witnessRetained_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeWitnessPacketReentry.RetainedClass v k) : NewTypes v k :=
  capturedPartner_into_newTypes k (Fresh.NativeWitnessPacketReentry.retained_into_partner h)

#print axioms witnessRetained_into_newTypes

theorem witnessRecovered_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeWitnessPacketReentry.RecoveredClass v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeWitnessPacketReentry.recovered_into_canonical h)

#print axioms witnessRecovered_into_newTypes

theorem packetExtremeRecovery_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativePacketExtremeRecovery.ExtremeClass v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativePacketExtremeRecovery.extreme_into_canonical h)

#print axioms packetExtremeRecovery_into_newTypes

theorem narrowBandRetained_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeNarrowCaptureBlock.RetainedBandClass v k) : NewTypes v k :=
  currentLabelRetained_into_newTypes k (Fresh.NativeNarrowCaptureBlock.retained_into_current h)

#print axioms narrowBandRetained_into_newTypes

theorem narrowBandRecovered_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeNarrowCaptureBlock.RecoveredBandClass v k) : NewTypes v k :=
  currentLabelRecovered_into_newTypes k (Fresh.NativeNarrowCaptureBlock.recovered_into_current h)

#print axioms narrowBandRecovered_into_newTypes

theorem quietReversal_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeQuietReversalFamily.Class v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k
    (Fresh.NativeOpeningReversalArrangement.pairRecovery_into_canonical
      (Fresh.NativeQuietReversalFamily.class_into_recovery h))

#print axioms quietReversal_into_newTypes

theorem quietReversalScaled_into_typesUp {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeQuietReversalFamily.ScaledClass v k) : TypesUp v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact ⟨c,hc,Or.inr (quietReversal_into_newTypes k hbase)⟩

#print axioms quietReversalScaled_into_typesUp

theorem quietReversalScaled_not_reduced {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeQuietReversalFamily.ScaledClass v k) : ¬ReducedAdmissible v k := by
  intro hr
  exact hr.2 (quietReversalScaled_into_typesUp k h)

#print axioms quietReversalScaled_not_reduced

theorem reversalCell_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReversalCellEnvelope.Class v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k
    (Fresh.NativeOpeningReversalArrangement.pairRecovery_into_canonical
      (Fresh.NativeReversalCellEnvelope.class_into_recovery h))

#print axioms reversalCell_into_newTypes

theorem reversalCellScaled_into_typesUp {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReversalCellEnvelope.ScaledClass v k) : TypesUp v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact ⟨c,hc,Or.inr (reversalCell_into_newTypes k hbase)⟩

#print axioms reversalCellScaled_into_typesUp

theorem reversalCellScaled_not_reduced {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReversalCellEnvelope.ScaledClass v k) : ¬ReducedAdmissible v k := by
  intro hr
  exact hr.2 (reversalCellScaled_into_typesUp k h)

#print axioms reversalCellScaled_not_reduced


theorem arbitraryThirdReversal_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeArbitraryThirdReversal.Class v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeArbitraryThirdReversal.class_into_canonical h)

#print axioms arbitraryThirdReversal_into_newTypes

theorem arbitraryThirdReversalScaled_into_typesUp {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeArbitraryThirdReversal.ScaledClass v k) : TypesUp v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact ⟨c,hc,Or.inr (arbitraryThirdReversal_into_newTypes k hbase)⟩

#print axioms arbitraryThirdReversalScaled_into_typesUp

theorem arbitraryThirdReversalScaled_not_reduced {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeArbitraryThirdReversal.ScaledClass v k) : ¬ReducedAdmissible v k := by
  intro hr
  exact hr.2 (arbitraryThirdReversalScaled_into_typesUp k h)

#print axioms arbitraryThirdReversalScaled_not_reduced


theorem capturedReversal_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeCapturedReversalFamily.Class v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeCapturedReversalFamily.class_into_canonical h)

#print axioms capturedReversal_into_newTypes

theorem capturedReversalScaled_into_typesUp {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeCapturedReversalFamily.ScaledClass v k) : TypesUp v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact ⟨c,hc,Or.inr (capturedReversal_into_newTypes k hbase)⟩

#print axioms capturedReversalScaled_into_typesUp

theorem capturedReversalScaled_not_reduced {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeCapturedReversalFamily.ScaledClass v k) : ¬ReducedAdmissible v k := by
  intro hr
  exact hr.2 (capturedReversalScaled_into_typesUp k h)

#print axioms capturedReversalScaled_not_reduced


theorem suppliedReversal_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeSuppliedReversalArrangement.Class v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeSuppliedReversalArrangement.class_into_canonical h)

#print axioms suppliedReversal_into_newTypes

theorem suppliedReversalScaled_into_typesUp {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeSuppliedReversalArrangement.ScaledClass v k) : TypesUp v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact ⟨c,hc,Or.inr (suppliedReversal_into_newTypes k hbase)⟩

#print axioms suppliedReversalScaled_into_typesUp

theorem suppliedReversalScaled_not_reduced {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeSuppliedReversalArrangement.ScaledClass v k) : ¬ReducedAdmissible v k := by
  intro hr
  exact hr.2 (suppliedReversalScaled_into_typesUp k h)

#print axioms suppliedReversalScaled_not_reduced


theorem reversalBranch_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReversalBranchArrangement.Class v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeReversalBranchArrangement.class_into_canonical h)

#print axioms reversalBranch_into_newTypes

theorem reversalBranchScaled_into_typesUp {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReversalBranchArrangement.ScaledClass v k) : TypesUp v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact ⟨c,hc,Or.inr (reversalBranch_into_newTypes k hbase)⟩

#print axioms reversalBranchScaled_into_typesUp

theorem reversalBranchScaled_not_reduced {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReversalBranchArrangement.ScaledClass v k) : ¬ReducedAdmissible v k := by
  intro hr
  exact hr.2 (reversalBranchScaled_into_typesUp k h)

#print axioms reversalBranchScaled_not_reduced


theorem clearWitness_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeClearWitnessArrangement.Class v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeClearWitnessArrangement.class_into_canonical h)

#print axioms clearWitness_into_newTypes

theorem clearWitnessScaled_into_typesUp {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeClearWitnessArrangement.ScaledClass v k) : TypesUp v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact ⟨c,hc,Or.inr (clearWitness_into_newTypes k hbase)⟩

#print axioms clearWitnessScaled_into_typesUp

theorem clearWitnessScaled_not_reduced {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeClearWitnessArrangement.ScaledClass v k) : ¬ReducedAdmissible v k := by
  intro hr
  exact hr.2 (clearWitnessScaled_into_typesUp k h)

#print axioms clearWitnessScaled_not_reduced


theorem clearRebound_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeClearReboundArrangement.Class v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeClearReboundArrangement.class_into_canonical h)

#print axioms clearRebound_into_newTypes

theorem clearReboundScaled_into_typesUp {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeClearReboundArrangement.ScaledClass v k) : TypesUp v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact ⟨c,hc,Or.inr (clearRebound_into_newTypes k hbase)⟩

#print axioms clearReboundScaled_into_typesUp

theorem clearReboundScaled_not_reduced {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeClearReboundArrangement.ScaledClass v k) : ¬ReducedAdmissible v k := by
  intro hr
  exact hr.2 (clearReboundScaled_into_typesUp k h)

#print axioms clearReboundScaled_not_reduced


theorem returnedGrid_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReturnedGridArrangement.Class v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeReturnedGridArrangement.class_into_canonical h)

#print axioms returnedGrid_into_newTypes

theorem returnedGridScaled_into_typesUp {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReturnedGridArrangement.ScaledClass v k) : TypesUp v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact ⟨c,hc,Or.inr (returnedGrid_into_newTypes k hbase)⟩

#print axioms returnedGridScaled_into_typesUp

theorem returnedGridScaled_not_reduced {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeReturnedGridArrangement.ScaledClass v k) : ¬ReducedAdmissible v k := by
  intro hr
  exact hr.2 (returnedGridScaled_into_typesUp k h)

#print axioms returnedGridScaled_not_reduced


theorem doubleGrid_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeDoubleGridArrangement.Class v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeDoubleGridArrangement.class_into_canonical h)

#print axioms doubleGrid_into_newTypes

theorem doubleGridScaled_into_typesUp {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeDoubleGridArrangement.ScaledClass v k) : TypesUp v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact ⟨c,hc,Or.inr (doubleGrid_into_newTypes k hbase)⟩

#print axioms doubleGridScaled_into_typesUp

theorem doubleGridScaled_not_reduced {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeDoubleGridArrangement.ScaledClass v k) : ¬ReducedAdmissible v k := by
  intro hr
  exact hr.2 (doubleGridScaled_into_typesUp k h)

#print axioms doubleGridScaled_not_reduced


theorem upperGrid_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeUpperGridArrangement.Class v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeUpperGridArrangement.class_into_canonical h)

#print axioms upperGrid_into_newTypes

theorem upperGridScaled_into_typesUp {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeUpperGridArrangement.ScaledClass v k) : TypesUp v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact ⟨c,hc,Or.inr (upperGrid_into_newTypes k hbase)⟩

#print axioms upperGridScaled_into_typesUp

theorem upperGridScaled_not_reduced {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeUpperGridArrangement.ScaledClass v k) : ¬ReducedAdmissible v k := by
  intro hr
  exact hr.2 (upperGridScaled_into_typesUp k h)

#print axioms upperGridScaled_not_reduced


theorem upperPair_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeUpperPairArrangement.Class v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeUpperPairArrangement.class_into_canonical h)

#print axioms upperPair_into_newTypes

theorem upperPairScaled_into_typesUp {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeUpperPairArrangement.ScaledClass v k) : TypesUp v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact ⟨c,hc,Or.inr (upperPair_into_newTypes k hbase)⟩

#print axioms upperPairScaled_into_typesUp

theorem upperPairScaled_not_reduced {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeUpperPairArrangement.ScaledClass v k) : ¬ReducedAdmissible v k := by
  intro hr
  exact hr.2 (upperPairScaled_into_typesUp k h)

#print axioms upperPairScaled_not_reduced


theorem phaseOrigin_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativePhaseOriginArrangement.Class v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativePhaseOriginArrangement.class_into_canonical h)

#print axioms phaseOrigin_into_newTypes

theorem phaseOriginScaled_into_typesUp {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativePhaseOriginArrangement.ScaledClass v k) : TypesUp v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact ⟨c,hc,Or.inr (phaseOrigin_into_newTypes k hbase)⟩

#print axioms phaseOriginScaled_into_typesUp

theorem phaseOriginScaled_not_reduced {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativePhaseOriginArrangement.ScaledClass v k) : ¬ReducedAdmissible v k := by
  intro hr
  exact hr.2 (phaseOriginScaled_into_typesUp k h)

#print axioms phaseOriginScaled_not_reduced


theorem tightCore_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeTightReboundCore.Class v k) : NewTypes v k :=
  upperPair_into_newTypes k (Fresh.NativeTightReboundCore.class_into_pair h)

#print axioms tightCore_into_newTypes

theorem tightCoreScaled_into_typesUp {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeTightReboundCore.ScaledClass v k) : TypesUp v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact ⟨c,hc,Or.inr (tightCore_into_newTypes k hbase)⟩

#print axioms tightCoreScaled_into_typesUp

theorem tightCoreScaled_not_reduced {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeTightReboundCore.ScaledClass v k) : ¬ReducedAdmissible v k := by
  intro hr
  exact hr.2 (tightCoreScaled_into_typesUp k h)

#print axioms tightCoreScaled_not_reduced

theorem upperTriple_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeUpperTripleArrangement.Class v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeUpperTripleArrangement.class_into_canonical h)

#print axioms upperTriple_into_newTypes

theorem upperTripleScaled_into_typesUp {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeUpperTripleArrangement.ScaledClass v k) : TypesUp v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact ⟨c,hc,Or.inr (upperTriple_into_newTypes k hbase)⟩

#print axioms upperTripleScaled_into_typesUp

theorem upperTripleScaled_not_reduced {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeUpperTripleArrangement.ScaledClass v k) : ¬ReducedAdmissible v k := by
  intro hr
  exact hr.2 (upperTripleScaled_into_typesUp k h)

#print axioms upperTripleScaled_not_reduced


theorem fourthReversal_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeFourthReversalArrangement.Class v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeFourthReversalArrangement.class_into_canonical h)

#print axioms fourthReversal_into_newTypes

theorem fourthReversalScaled_into_typesUp {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeFourthReversalArrangement.ScaledClass v k) : TypesUp v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact ⟨c,hc,Or.inr (fourthReversal_into_newTypes k hbase)⟩

#print axioms fourthReversalScaled_into_typesUp

theorem fourthReversalScaled_not_reduced {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeFourthReversalArrangement.ScaledClass v k) : ¬ReducedAdmissible v k := by
  intro hr
  exact hr.2 (fourthReversalScaled_into_typesUp k h)

#print axioms fourthReversalScaled_not_reduced


theorem recoveredSecond_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeRecoveredSecondArrangement.Class v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeRecoveredSecondArrangement.class_into_canonical h)

#print axioms recoveredSecond_into_newTypes

theorem recoveredSecondScaled_into_typesUp {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeRecoveredSecondArrangement.ScaledClass v k) : TypesUp v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact ⟨c,hc,Or.inr (recoveredSecond_into_newTypes k hbase)⟩

#print axioms recoveredSecondScaled_into_typesUp

theorem recoveredSecondScaled_not_reduced {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeRecoveredSecondArrangement.ScaledClass v k) : ¬ReducedAdmissible v k := by
  intro hr
  exact hr.2 (recoveredSecondScaled_into_typesUp k h)

#print axioms recoveredSecondScaled_not_reduced


theorem hierarchicalFourth_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeHierarchicalFourthArrangement.Class v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeHierarchicalFourthArrangement.class_into_canonical h)

#print axioms hierarchicalFourth_into_newTypes

theorem hierarchicalFourthScaled_into_typesUp {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeHierarchicalFourthArrangement.ScaledClass v k) : TypesUp v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact ⟨c,hc,Or.inr (hierarchicalFourth_into_newTypes k hbase)⟩

#print axioms hierarchicalFourthScaled_into_typesUp

theorem hierarchicalFourthScaled_not_reduced {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeHierarchicalFourthArrangement.ScaledClass v k) : ¬ReducedAdmissible v k := by
  intro hr
  exact hr.2 (hierarchicalFourthScaled_into_typesUp k h)

#print axioms hierarchicalFourthScaled_not_reduced


theorem comparableFourth_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeComparableFourthArrangement.Class v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeComparableFourthArrangement.class_into_canonical h)

#print axioms comparableFourth_into_newTypes

theorem comparableFourthScaled_into_typesUp {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeComparableFourthArrangement.ScaledClass v k) : TypesUp v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact ⟨c,hc,Or.inr (comparableFourth_into_newTypes k hbase)⟩

#print axioms comparableFourthScaled_into_typesUp

theorem comparableFourthScaled_not_reduced {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeComparableFourthArrangement.ScaledClass v k) : ¬ReducedAdmissible v k := by
  intro hr
  exact hr.2 (comparableFourthScaled_into_typesUp k h)

#print axioms comparableFourthScaled_not_reduced


theorem fastSecondReset_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeFastSecondResetArrangement.Class v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeFastSecondResetArrangement.class_into_canonical h)

#print axioms fastSecondReset_into_newTypes

theorem fastSecondResetScaled_into_typesUp {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeFastSecondResetArrangement.ScaledClass v k) : TypesUp v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact ⟨c,hc,Or.inr (fastSecondReset_into_newTypes k hbase)⟩

#print axioms fastSecondResetScaled_into_typesUp

theorem fastSecondResetScaled_not_reduced {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeFastSecondResetArrangement.ScaledClass v k) : ¬ReducedAdmissible v k := by
  intro hr
  exact hr.2 (fastSecondResetScaled_into_typesUp k h)

#print axioms fastSecondResetScaled_not_reduced


theorem fastSecondReturn_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeFastSecondReturnArrangement.Class v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeFastSecondReturnArrangement.class_into_canonical h)

#print axioms fastSecondReturn_into_newTypes

theorem fastSecondReturnScaled_into_typesUp {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeFastSecondReturnArrangement.ScaledClass v k) : TypesUp v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact ⟨c,hc,Or.inr (fastSecondReturn_into_newTypes k hbase)⟩

#print axioms fastSecondReturnScaled_into_typesUp

theorem fastSecondReturnScaled_not_reduced {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeFastSecondReturnArrangement.ScaledClass v k) : ¬ReducedAdmissible v k := by
  intro hr
  exact hr.2 (fastSecondReturnScaled_into_typesUp k h)

#print axioms fastSecondReturnScaled_not_reduced


theorem fastSecondFourth_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeFastSecondFourthArrangement.Class v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeFastSecondFourthArrangement.class_into_canonical h)

#print axioms fastSecondFourth_into_newTypes

theorem fastSecondFourthScaled_into_typesUp {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeFastSecondFourthArrangement.ScaledClass v k) : TypesUp v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact ⟨c,hc,Or.inr (fastSecondFourth_into_newTypes k hbase)⟩

#print axioms fastSecondFourthScaled_into_typesUp

theorem fastSecondFourthScaled_not_reduced {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeFastSecondFourthArrangement.ScaledClass v k) : ¬ReducedAdmissible v k := by
  intro hr
  exact hr.2 (fastSecondFourthScaled_into_typesUp k h)

#print axioms fastSecondFourthScaled_not_reduced


theorem smallFourth_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeSmallFourthArrangement.Class v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeSmallFourthArrangement.class_into_canonical h)

#print axioms smallFourth_into_newTypes

theorem smallFourthScaled_into_typesUp {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeSmallFourthArrangement.ScaledClass v k) : TypesUp v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact ⟨c,hc,Or.inr (smallFourth_into_newTypes k hbase)⟩

#print axioms smallFourthScaled_into_typesUp

theorem smallFourthScaled_not_reduced {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeSmallFourthArrangement.ScaledClass v k) : ¬ReducedAdmissible v k := by
  intro hr
  exact hr.2 (smallFourthScaled_into_typesUp k h)

#print axioms smallFourthScaled_not_reduced


theorem arbitraryFourth_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeArbitraryFourthArrangement.Class v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeArbitraryFourthArrangement.class_into_canonical h)

#print axioms arbitraryFourth_into_newTypes

theorem arbitraryFourthScaled_into_typesUp {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeArbitraryFourthArrangement.ScaledClass v k) : TypesUp v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact ⟨c,hc,Or.inr (arbitraryFourth_into_newTypes k hbase)⟩

#print axioms arbitraryFourthScaled_into_typesUp

theorem arbitraryFourthScaled_not_reduced {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeArbitraryFourthArrangement.ScaledClass v k) : ¬ReducedAdmissible v k := by
  intro hr
  exact hr.2 (arbitraryFourthScaled_into_typesUp k h)

#print axioms arbitraryFourthScaled_not_reduced


theorem twoGridFourth_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeTwoGridFourthArrangement.Class v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeTwoGridFourthArrangement.class_into_canonical h)

#print axioms twoGridFourth_into_newTypes

theorem twoGridFourthScaled_into_typesUp {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeTwoGridFourthArrangement.ScaledClass v k) : TypesUp v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact ⟨c,hc,Or.inr (twoGridFourth_into_newTypes k hbase)⟩

#print axioms twoGridFourthScaled_into_typesUp

theorem twoGridFourthScaled_not_reduced {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeTwoGridFourthArrangement.ScaledClass v k) : ¬ReducedAdmissible v k := by
  intro hr
  exact hr.2 (twoGridFourthScaled_into_typesUp k h)

#print axioms twoGridFourthScaled_not_reduced


theorem fourUpper_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeFourUpperArrangement.Class v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeFourUpperArrangement.class_into_canonical h)

#print axioms fourUpper_into_newTypes

theorem fourUpperScaled_into_typesUp {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeFourUpperArrangement.ScaledClass v k) : TypesUp v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact ⟨c,hc,Or.inr (fourUpper_into_newTypes k hbase)⟩

#print axioms fourUpperScaled_into_typesUp

theorem fourUpperScaled_not_reduced {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeFourUpperArrangement.ScaledClass v k) : ¬ReducedAdmissible v k := by
  intro hr
  exact hr.2 (fourUpperScaled_into_typesUp k h)

#print axioms fourUpperScaled_not_reduced

theorem mixedObserverGridSeeds_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeMixedObserverGridSeeds.Class v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeMixedObserverGridSeeds.class_into_canonical h)

#print axioms mixedObserverGridSeeds_into_newTypes

theorem mixedObserverGridSeedsScaled_into_typesUp {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeMixedObserverGridSeeds.ScaledClass v k) : TypesUp v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact ⟨c,hc,Or.inr (mixedObserverGridSeeds_into_newTypes k hbase)⟩

#print axioms mixedObserverGridSeedsScaled_into_typesUp

theorem mixedObserverGridSeedsScaled_not_reduced {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeMixedObserverGridSeeds.ScaledClass v k) : ¬ReducedAdmissible v k := by
  intro hr
  exact hr.2 (mixedObserverGridSeedsScaled_into_typesUp k h)

#print axioms mixedObserverGridSeedsScaled_not_reduced

theorem seedResidueProduct_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeSeedResidueProduct.Class v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeSeedResidueProduct.class_into_canonical h)

#print axioms seedResidueProduct_into_newTypes

theorem seedResidueProductScaled_into_typesUp {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeSeedResidueProduct.ScaledClass v k) : TypesUp v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact ⟨c,hc,Or.inr (seedResidueProduct_into_newTypes k hbase)⟩

#print axioms seedResidueProductScaled_into_typesUp

theorem seedResidueProductScaled_not_reduced {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeSeedResidueProduct.ScaledClass v k) : ¬ReducedAdmissible v k := by
  intro hr
  exact hr.2 (seedResidueProductScaled_into_typesUp k h)

#print axioms seedResidueProductScaled_not_reduced

theorem commonOpeningGridBands_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeCommonOpeningGridBands.Class v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeCommonOpeningGridBands.class_into_canonical h)

#print axioms commonOpeningGridBands_into_newTypes

theorem commonOpeningGridBandsScaled_into_typesUp {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeCommonOpeningGridBands.ScaledClass v k) : TypesUp v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact ⟨c,hc,Or.inr (commonOpeningGridBands_into_newTypes k hbase)⟩

#print axioms commonOpeningGridBandsScaled_into_typesUp

theorem commonOpeningGridBandsScaled_not_reduced {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeCommonOpeningGridBands.ScaledClass v k) : ¬ReducedAdmissible v k := by
  intro hr
  exact hr.2 (commonOpeningGridBandsScaled_into_typesUp k h)

#print axioms commonOpeningGridBandsScaled_not_reduced


theorem uniformOpeningCells_into_newTypes {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeUniformOpeningCells.Class v k) : NewTypes v k :=
  canonicalReturn_into_newTypes k (Fresh.NativeUniformOpeningCells.class_into_canonical h)

#print axioms uniformOpeningCells_into_newTypes

theorem uniformOpeningCellsScaled_into_typesUp {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeUniformOpeningCells.ScaledClass v k) : TypesUp v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact ⟨c,hc,Or.inr (uniformOpeningCells_into_newTypes k hbase)⟩

#print axioms uniformOpeningCellsScaled_into_typesUp

theorem uniformOpeningCellsScaled_not_reduced {v : Fin 8 → ℝ} (k : Fin 8)
    (h : Fresh.NativeUniformOpeningCells.ScaledClass v k) : ¬ReducedAdmissible v k := by
  intro hr
  exact hr.2 (uniformOpeningCellsScaled_into_typesUp k h)

#print axioms uniformOpeningCellsScaled_not_reduced


end Fresh.ArrangementTypesOct26
