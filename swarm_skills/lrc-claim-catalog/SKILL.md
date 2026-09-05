---
name: lrc-claim-catalog
description: Seed and maintain a structured claim queue for LRC and related tracks from registry files. Use when building or refreshing `registry/claim_seed_queue.csv`, prioritizing artifacts for Catalog Agent ingestion, or generating controlled Phase 1 batches from `track_map.csv`.
---

# LRC Claim Catalog

Run this skill to produce deterministic seed queues from classified artifacts.

## Workflow
1. Confirm source registries exist:
- `registry/track_map.csv`
- `registry/corpus_manifest.csv` (optional for cross-check)
2. Run queue seeding script.
3. Check queue size, priority distribution, and top entries.
4. Commit queue update only after coordinator approval.

## Quick Start
```bash
python3 scripts/seed_claim_queue.py \
  --track-map "/Users/trentpalelei/Desktop/Math Ex/registry/track_map.csv" \
  --output "/Users/trentpalelei/Desktop/Math Ex/registry/claim_seed_queue.csv" \
  --track LRC \
  --batch-size 80
```

## Options
- `--track`: Any track in `track_map.csv` (default `LRC`)
- `--batch-size`: Number of seeded artifacts
- `--min-confidence`: Minimum `track_confidence`
- `--dry-run`: Preview without writing file

## Quality Rules
1. Keep seeds atomic and evidence-first.
2. Prioritize core proofs and primary evidence (`P1`) before auxiliary files.
3. Do not remove existing registry artifacts; only refresh queue output.

## References
- For output schema and priority rules, read `references/claim_seed_schema.md`.
