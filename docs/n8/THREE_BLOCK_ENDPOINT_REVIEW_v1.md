# Independent endpoint-singleton source review

Rules: 1–4, 8–18. No correctness-affecting gap found in the five fixed proof bodies, generic assembly or physical consumer. Root-owned source and catalogue were not edited.

Exact representation domain: p=1,1≤q≤5,r=7−q≥2, originalg≥1,h>0,g+h≤2 and the forward independent-lap triangle at integer m≥1. The physical class explicitly retains positive distinct speeds, arbitrary signed affine scale, drift, mirror and labels. The representation is a left singleton; signed physical mirroring also admits corresponding reflected physical arrangements. No blanket claim for all endpoint-singleton configurations is present.

Every signed reading in all five fixed bodies was checked. The generator coordinate list `(1,0,0)`, `(i,1,0)` for1≤i≤q, `(i−1,1,1)` fori≥q+1 matches the Lean speed definition exactly. All280 explicit signed laps match the independently derived coordinate differences. Direct bands use0 or−1 by reading sign. The carried bands use the coordinate difference timesm plus the independent gap lap coefficients and the exact signed band offset.

The singleton at label0 usesT=1/8: its least reading isg≥1 and its greatest is5+g+h≤7. Carried subject labels are `{1,q,q+1}` (only two distinct labels whenq=1). At a boundary subject with compressed coordinate1, the maximal integer contribution can be5/8, but it carries only a single residualu orv≤1/4; it therefore still fits7/8. Other carried readings use the established residual triangleu,v≥1/8,u+v≤3/8. No reading is omitted.

`train_flank_endpoint_singleton_review_v1.py` independently replays the selected440 original-map controls and1800 large-index controls, reconstructing the entire original cascade and comparing its saved history exactly. It verifies the actual **prescribed role-specific reference** from the Lean body, which is stronger than merely testing whether direct OR carried time clears. All2240 controls pass, maximum observed5 moves diagnostic only. The five controls outside FixedRList remain exact overlap diagnostics, with no assertion of whole-class exclusion. Full review rows are saved in its JSON output.

`Fresh/TrainFlankEndpointSingletonAudit.lean` compiled successfully and prints all seven endpoints with exactly `[propext, Classical.choice, Quot.sound]`. Scanner reports no sorry/native_decide/axiom/admit/unsafe declarations. The wider root singleton map's failures outside this stated domain remain unaffected.
