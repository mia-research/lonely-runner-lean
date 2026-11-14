# Three-block partition mechanism

Rules: 1–4, 8–18. Exact original-cascade mapping preceded symbolic proof generation. This version preserves the root-owned Wide, Polynomial and catalogue files.

## Source review

Full `ThreeBlockWideLaps.lean` was compared with the prior IndependentLaps proof. The only mathematical hypothesis change is the total original-gap bound from1/3 to2. The four direct subjects in2+4+2 retain every distance in[1,7] at time1/8; the four gap-adjacent subjects retain the same independent-lap residual triangle. No correctness-affecting gap was found. The physical class retains positive distinct speeds, signed scale, drift and relabeling. Imported axioms for Wide and its two class joins were checked independently in `TrainFlankThreeBlockWideAudit.lean`, all standard.

## Six ordered partitions

For block lengths p,q,r≥2 with p+q+r=8, use physical speeds

- first block: `c+1,...,c+p`;
- second block: `c+p+g,...,c+p+q−1+g`;
- third block: `c+p+q−1+g+h,...,c+6+g+h`.

The original cross-block gaps are g>0 and h>0; internal AP step is1. The six ordered lengths are2+2+4,2+3+3,2+4+2,3+2+3,3+3+2,4+2+2. No stationary physical runner is introduced.

The same explicit independent-lap input conditions suffice in all six cases:

`m≥1`, `g+h≤2`, `8a+1≤(8m+1)g`, `8b+1≤(8m+1)h`,
`(8m+1)(g+h)≤8(a+b)+3`, with integer m,a,b.

The theorem does not assert these integer labels exist for arbitrary positive g,h.

## Mechanism derived from controls

The four gap-adjacent subject labels are `{p−1,p,p+q−1,p+q}`. At `T=m+1/8`, put `u=gT−a`, `v=hT−b`. The input conditions give `u,v≥1/8` and `u+v≤3/8`. Each positive reading from one of these subjects is `D+eg*g+eh*h`, where `0≤D≤4`, `eg,eh∈{0,1}`, and at least one of D,eg,eh is positive. Its fractional expression is `D/8+eg*u+eh*v`, within[1/8,7/8]. Negative signed readings use the reflected closed integer band. Every lap is explicitly `D*m+eg*a+eh*b`, with−1 for reflected bands.

The other four subjects have minimum reading at least1 and total diameter `5+g+h≤7`. They clear directly atT=1/8. Gap-adjacent subjects may also clear there for particular inputs; the role classification identifies the proof obligation, not a claim that their first isolation is later.

## Original-cascade controls and overlap

Run `python3 experiments/n8/train_flank_three_partition_map_v1.py`. Full original histories, blockers, boundary setters, readings, outputs and named comparisons are saved in the matching JSON.

-8064 physical subject controls,1344 for each ordered partition, all positive and distinct.
-4032 direct AP roles and4032 gap-adjacent roles; all named comparisons clear.
-4320 controls also clear at1/8, matching their actual output there.
-Zero exceptions; maximum7 observed moves is diagnostic only.
-8060 controls belong to the exact checked FixedRList finite class of368 candidate ratios.
-240 controls have a natural two-AP merge because g=1 orh=1. Alternative representations by every known class were not excluded.

Four controls are outside that FixedRList and have no such natural merge. They all have g=h=1/6 and land at9/8 from initial3/4:

| Partition | Subject | Boundary setter labels |
|---|---:|---|
|2+2+4|1|4,3,0|
|3+2+3|2|5,4,1|
|3+2+3|5|2,3,6|
|4+2+2|6|3,4,7|

These are exact finite-class nonmembership controls, not exclusion from every earlier physical class and not universal proof premises.

## Sources and complement

`Fresh/ThreeBlockPartitions.lean` contains six fixed-partition band proofs, their generic p/q assembly, and `ThreeBlockPartitionsClass` with its physical consumer. Its reproducible generator is `train_flank_three_partition_gen_v1.py`. `TrainFlankPartitionJoins.lean` embeds the existing2+4+2 Wide class and hence IndependentLaps and Polynomial classes, preventing duplicate family counts.

The complement includes arbitrary gaps for which no residual-triangle lap witness is yet derived, totalgap>2 outside other established classes, and general unequal-step three-block arrangements. No full n=8 claim is made.

## Kernel check manifest

Forward module compiled successfully. All six fixed-partition theorems, `partitions_all_subjects` and `threeBlockPartitions_isolation` print only the standard axioms. The three kernel-checked class joins `wide_into_partitions`, `independent_into_partitions`, `polynomial_into_partitions` also compile with only `[propext, Classical.choice, Quot.sound]`. Source scanners report no sorry/native_decide/axiom/admit/unsafe declarations. The forward module's printer abbreviates `Classical.choice` as `choice` because `Classical` is open; the join endpoints print its qualified name.
