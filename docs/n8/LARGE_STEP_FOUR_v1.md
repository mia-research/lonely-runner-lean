# Large-step packet cycle, v1

Rules: 1–4, 8–18. Source: actual upper-opening tests before formalisation.

- [OBS, exact] `large_step_four_v1.py` checks72 actual full-cascade controls at b=15/2,x=b, both sides of the ceiling jumps b=8k+6 for k=1,2,5,20,100, and four x/b ratios; no exceptions, maximum three actual moves. Full physical readings and boundary data are saved in JSON.
- [L] `Fresh/LargeStepFour.lean`: for every real b≥15/2 and x≥b, `mixedTrain x b={1,2,3,x,x+b,x+2b,x+3b}` has an explicit clear upper opening. Setq=ceil(b/8−3/4), lo=(q+3/4)/b andhi=(q+1)/b; this entire phase interval stays in the fixed core's `[1/8,7/24]` window.
- [L] Since x+3b≥4b, the upper reference's next opening occurs beforelo+1/(x+3b)≤hi. Each packet reading retains its own lapN−j(q+1), with residual1/8+j(q+1−bT) in `[1/8,7/8]` for j=0…3.
- [L] All three theorem endpoints, including the pointwise physical-consumer wrapper, compile cleanly and print exactly `propext, Classical.choice, Quot.sound`; source scan zero placeholders/native_decide/unsafe.
- [PROVISIONAL: counting tool] supports exact ceiling/opening placement; no density or uniform cascade cap. Independent laps grow throughq without demanding new proofs.
