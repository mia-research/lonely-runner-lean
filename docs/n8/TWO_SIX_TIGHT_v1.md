# Sharper two-plus-six original gap, v1

Rules: 1–4, 8–18. New file preserves all previous theorem APIs and source constants.

- [L] `Fresh/TwoSixTight.lean`, `two_six_low_tight`: everyb>0 andx≥9max(1,b) clears fixed reading1 and allsix packet readingsx+j*b,j=0…5. The established middle/large branches already need9b; the smallb branch follows the same exact base opening with5b(1/8+1/9)<3/4.
- [L] `two_six_tight_all_subjects(c,A,b)` proves every subject of `UnequalAPArrangement.speeds c A 1 b 2` isolated for everyb>0 andoriginalgapA−1≥15max(1,b). Both low subjects use9max; all upper subjects retain ownAPcore1…5 atstepb and reuseAPCorePair, whose exact condition30b≤2x needs onlyx≥15b.
- [L] Both endpoints compile cleanly, print exactly `propext, Classical.choice, Quot.sound`, and pass zero-placeholder/native_decide/unsafe scans; no existing source, pins, gates or commits changed.
- [OBS, exact] `two_six_tight_v1.py` checks the ORIGINAL cascade and the explicit native named candidates before proof:816 physical subject controls atgap15max equality and enlargements,17 low9max controls, b from1/1000 through100, both sides of phase/ceiling cuts, two positive scales; no exceptions. The upper candidate reproduces FastPairReal.pair_window's quarter-band then band-point construction exactly.
- [TREE] This removes the additional original-gap strip15max≤g<20max; smaller gaps remain outside this theorem unless handled by another established family. The AP-core-plus-pair family is reused, not counted again as previously unproved.
- [PROVISIONAL: counting tool] inherited named boundary selection; [PROVISIONAL: covering] inherited pair-window fit and finite step split. No density or universal cascade cap.
- [source found, next candidate] ExistingPairGapHalf.pair_gap_half gives a stronger1/(2a) pair gap; reusing it against the same core could supplyx≥10b andphysicalgap10max. That improvement is not claimed by this file.
