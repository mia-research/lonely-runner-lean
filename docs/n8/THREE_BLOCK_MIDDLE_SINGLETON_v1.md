# Middle singleton extension of three-block native phase bands

Rules: 1–4, 8–18. New files only. Root singleton maps and endpoint-singleton failures remain unchanged. No finite point-control novelty is asserted.

## Scope

The established physical speed function has block lengths p,q,r with p+q+r=8 and internal AP step1. The new generic range is **p≥2,q≥1,r≥2**. It adds four middle-singleton partitions2+1+5,3+1+4,4+1+3,5+1+2 to the six prior partitions. The old q≥2 theorem is consumed unchanged.

Both phase signs retain the original real gaps g,h>0, total original gap g+h≤2, and explicit unbounded integer lap conditions. The forward phase usesT=m+1/8 and the inequalities in THREE_BLOCK_PARTITIONS_v1; the reflected phase usesT=m−1/8 and the inequalities in THREE_BLOCK_REVERSE_PARTITIONS_v1. Existence of such lap labels for arbitrary gaps is not assumed or asserted.

The physical classes retain positive distinct speeds, signed affine scale, drift, mirror and arbitrary labels. The endpoint blocks still require at least2 runners. The root map contains624 subject controls for endpoint-singleton configurations clearing at neither old reference; these remain outside this extension.

## Actual cascade source and mechanism

Root's forward singleton map was read first. All four middle-singleton partitions passed608 original-subject controls each. The new independent map `train_flank_middle_singleton_map_v1.py` additionally checks the prescribed role-specific candidate and reflected phase before proof generation.

A singleton middle runner belongs to both gap boundaries, so the carried-subject set is now `{p−1,p,p+1}`, only three distinct subjects. The other five subjects have every distance in[1,7] and clear at1/8. The singleton itself has phase readings u andv to its two neighbours; the across-singleton reading between the two outer boundary subjects is u+v. The same native closed triangle u,v≥1/8,u+v≤3/8 controls all seven readings. Compressed AP coordinates remain between2 and5 for the carried subjects, so the previous maximal integer contribution4/8 still applies. This was checked from full actual outputs before formalization, not inferred from partition headlines alone.

## Exact control manifest

-4512 actual original-subject cascades and prescribed named comparisons, zero exceptions.
-2432 forward controls and2080 reflected controls.
-2820 direct AP roles and1692 carried roles.
-All4512 controls are in the checked368-candidate FixedRList finite class;384 have a natural two-AP merge. These are overlap counts and do not provide a strict new-space claim.
-Maximum6 observed cascade moves is diagnostic only.
-Full speeds, all seven readings, histories, blockers, setters, outputs and comparisons are retained in `train_flank_middle_singleton_map_v1.json`.

## Source manifest

-`Fresh/ThreeBlockMiddlePartitions.lean`: four fixed forward cases, generic `middle_partitions_all_subjects`, physical class and consumer.
-`Fresh/ThreeBlockReverseMiddlePartitions.lean`: four reflected cases, generic `reverse_middle_partitions_all_subjects`, physical class and consumer.
-`Fresh/TrainFlankMiddlePartitionJoins.lean`: previous six-partition class and rootWide class embed in the forward extension.
-`Fresh/TrainFlankReverseMiddlePartitionJoins.lean`: previous reflected six-partition class and rootReverse class embed in the reflected extension.
-Reproducible generators: `train_flank_middle_partition_gen_v1.py` and `train_flank_reverse_middle_partition_gen_v1.py`.

Each generated branch proves a symbolic real-parameter band inequality with an explicit integer lap; no finite numerical certificate appears as a hypothesis. The complement still includes endpoint-singleton configurations, independent gaps without a derived admissible lap witness, total gap beyond2, and general unequal internal steps unless settled by another class. No full n=8 claim is made.

## Kernel-check manifest

Both phase modules compiled successfully: four fixed-partition endpoints, generic endpoint and physical consumer each. Both class-join modules also compiled successfully. Qualified imported audits confirm exactly `[propext, Classical.choice, Quot.sound]` for generic endpoints and joins; all other printed endpoints have the same standard list. Each source scanner reports zero sorry/native_decide/axiom/admit/unsafe declarations. No existing APIs or root-owned files were edited. The generated modules retain harmless unused-tactic warnings where exact numeric goals close early.
