# Four fast readings at every positive step ratio, v1

Rules: 1–4, 8–18. Same physical subject, retained core and complete packet; actual cascade tests precede proof.

- [OBS, exact] `step_four_all_v1.py` passes144 exact parameter controls and all1152 physical subject cascades, including every finite phase-cut boundary and both adjacent1/64 perturbations, closed x=21b, and b=806+1/64; no exceptions, maximum five actual moves. These controls diagnose the proof rather than replace it.
- [L] `Fresh/StepFourAll.lean`, `step_four_all`: every real b≥1, x≥21b gives isolation of all seven readings `{1,2,3,x,x+b,x+2b,x+3b}`. `step_four_all_readings` supplies fixedj=1…3 and packetj=0…3 directly to the physical consumer.
- [L] Uniform upper-opening rule: choose a reference packet phaseα; x+3b≥24b puts the opening in phase `[α,α+1/24]`. Conditionsb≤8α and24α+1≤7b retain the fixed core in `[1/8,7/24]`.
- [L] The finite step ranges useα=1/4 throughb=2; α=5/12 throughb=10/3; α=5/8 throughb=5; α=3/4 throughb=6; α=5/4 throughb=15/2; the independent-lap large-step law supplies allb≥15/2. Every branch carries explicit packet lap labels and all equality edges.
- [L] All six new theorem endpoints compile cleanly and print exactly `propext, Classical.choice, Quot.sound`; no placeholders/native_decide/unsafe. New files only, no commit.
- [TREE] Root/agentC's physical consumer may swap the blocks and positively rescale: this family then supports four-plus-four AP blocks with arbitrary positive step ratio under gap≥21max(step1,step2). The all-subject physical theorem is assembled separately, rather than inferred from one subject's result.
- [PROVISIONAL: counting tool] supports explicit opening placement; [PROVISIONAL: covering] supports the finite STEP-PARAMETER split. No density, time-window covering, first-landing statement or universal arrangement cap is used.
- [OWED/complement] Smaller gaps and other block-size/step arrangements remain outside this theorem unless already handled by another established family. No universal n8 or finite-completeness claim is made.
