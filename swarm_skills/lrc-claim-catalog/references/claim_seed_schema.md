# Claim Seed Queue Schema

Output file: `registry/claim_seed_queue.csv`

Columns:
1. `claim_id`: Seed identifier (`SEED-<TRACK>-######`)
2. `source_artifact_id`: Artifact identifier from `track_map.csv`
3. `filename`: Source filename
4. `track`: Track label
5. `priority_note`: One of:
- `P1_core_proof_or_primary_evidence`
- `P2_supporting_or_replication`
- `P3_context_or_auxiliary`

Priority heuristics:
1. `P1`: Proof drafts, structural reduction docs, primary empirical validations.
2. `P2`: Replication data, supporting analyses.
3. `P3`: Context docs, notes, peripheral material.

Determinism rules:
1. Stable sorting by score descending, then filename ascending.
2. Fixed thresholds for priority buckets.
3. Explicit batch size.
