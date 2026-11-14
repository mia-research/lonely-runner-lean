# Two plus six AP blocks: native S2 reuse and gap9

Rules: 1–4, 8–18. This report is an additional versioned result, preserving the existing gap20, gap15 and gap10 modules and their APIs.

## Exact scope

`Fresh/TwoSixNine.lean` proves every physical subject for speeds

`c, c+1, c+A, c+A+b, ..., c+A+5b`

for every real `b>0` and the **closed original-gap condition** `A−1 ≥ 9 max(1,b)`. The physical class adds positivity, distinctness, arbitrary signed affine scale, drift, mirror and labels. Thus for positive internal steps `u,v`, the condition is original gap at least `9 max(u,v)`.

## Source mechanism and reuse

The two low subjects consume `TwoSixTight.two_six_low_tight`: a named first packet opening for `b≤8/21`, an actual interior packet anchor at the quarter phase for `8/21≤b≤2`, and a ceiling-selected independent packet lap for `b≥2`. This is the new low-role obligation established in the tighter source.

The upper six subjects are a frozen six-term AP with two arbitrary movers. These subjects were already settled by the native S2Complete framework. `frozen_six` dispatches the six concrete frozen-disparity sets `12345,1234,123,123,1234,12345`. The physical arrangement is normalized exactly by `b` to `twoMover ((c+A−b)/b) (c/b) ((c+1)/b) 0 7`, with display permutation `[0,7,1,2,3,4,5,6]`; positive scaling and relabeling transport back. The six frozen roles require no gap premise beyond the two movers being distinct from the particular frozen subject. This is reuse of established proof, not an assertion of six newly unknown subject types.

All seven readings remain present in each subject's isolation statement. No presumed future isolation, numerical approximation, density or cap is used. Boundary selectors and covering inherited from source modules retain their provisional counting-tool/covering tags.

## Exact regression before assembly

Reproduce with `python3 experiments/n8/two_six_nine_v1.py`.

- 816 original-cascade physical-subject controls: 17 rational step ratios, 3 gap factors, 2 physical scales, 8 subjects.
- 204 named low-subject candidate controls, with exact closed-boundary tests around `b=8/21`, `b=2` and `b=8`.
- Zero exceptions. Maximum observed cascade moves:19; this number is diagnostic and supplies no proof premise.
- Complete exact source paths, setters and landings are saved in `two_six_nine_v1.json`.

The companion `TwoSixTen.lean` reuses the existing `PairGapHalf.pair_gap_half` for a shorter first-window fit and proves gap10. Its 816 direct native pair-candidate checks are in `two_six_ten_v1.py/json`. This result was already underway when the stronger complete-S2 reuse was identified. It is preserved as a boundary-window companion; gap9 is the stronger physical result.

## Check manifest

- `Fresh.TwoSixNine.frozen_six`
- `Fresh.TwoSixNine.two_six_nine_all_subjects`
- `Fresh.TwoSixNine.twoSixNine_isolation`
- Companion: `Fresh.TwoSixTen.ap_core_pair_half`, `two_six_ten_all_subjects`.

Each endpoint is printed with `#print axioms`; only `propext`, `Classical.choice`, `Quot.sound` occur. The source scanner checks zero sorry/native_decide/axiom/admit/unsafe declarations.

## Complement

This theorem makes no claim that gap9 is necessary or optimal. Remaining unequal-step close-gap arrangements are not classified here. Existing same-step and other independently proved classes can settle portions of that complement. The full n=8 conjecture is not asserted.
