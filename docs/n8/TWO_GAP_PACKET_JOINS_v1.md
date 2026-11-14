# Packet proof review and near-subject containment

Rules: 1–4, 8–18. Root-owned PacketBand and catalogue remain untouched.

- [L] Full `TwoGapPacketBand.lean` review found no correctness-affecting gap: all four bit cases use exact closed integer bands. The zero-bit case derivesD≥1, and the other cases retain the residualu/v triangle withD≤4.
- [L] Positive unit scaling is exact: physical candidate time is `(m+1/8)/u`, u>0. The proof uses the absolute-disparity identity and cancelsu. It requires no distinct-absolute-reading hypothesis; repeated magnitudes are permitted while physical positivity/injectivity remain explicit in the class.
- [L] New `Fresh/TrainFlankPacketJoins.lean` derives the actual coefficient representation for near-gap subjects of all ten forward three-block partitions withp≥2,q≥1,p+q≤6. Ten structural helper proofs and generic `near_shape` retain every signed reading before taking its absolute value.
- [L] `NearGapSubject p q k` names the boundary labels `{p−1,p,p+q−1,p+q}`; it naturally has only three distinct labels whenq=1. No direct AP subject is forced into this predicate or the packet class.
- [L] `affine_near_into_packet` keeps physicalpositive/injectiveV, signed scalez≠0, driftB and relabelingσ, derives packet unit `|z|`, and proves `TwoGapPacketClass V k` for a near-labeled physical subject. No bound on originalg+h is needed for this near-subject containment.
- [L] `middle_near_into_packet` unpacks the existing `ThreeBlockMiddlePartitionsClass` witness and returnsp,q,σ with packet-class membership for every corresponding near subject. Existing direct-subject proofs remain available separately; no whole-class-to-every-subject packet inclusion is claimed.
- [L] All13 new endpoints compiled successfully and print standard axioms. The two imported PacketBand endpoints were audited explicitly with qualified names, exactly `[propext, Classical.choice, Quot.sound]`. Source scanner reports zero sorry/native_decide/axiom/admit/unsafe declarations.
- [SOURCE] Reproducible structural generator: `experiments/n8/train_flank_packet_joins_gen_v1.py`. It emits coefficient identities and exact absolute-value proofs, not numerical time certificates. Actual original-cascade mapping preceded the root packet lemma and is recorded in TWO_GAP_PACKET_MAP_v1.
- [OBS] Harmless unused/unreachable-tactic warnings occur where numeric identities close before a later tactic. The statements and kernel checks do not depend on suppressing these warnings.
- [OWED] No arbitrary-reading representation theorem or full exclusion from prior classes is asserted. This join records shared structure and prevents treating its near-role instances as independent packet families.
