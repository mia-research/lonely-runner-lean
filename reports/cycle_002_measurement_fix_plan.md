# Measurement Fix Pass (Cycle 002)

Generated: 2026-02-25T23:40:27Z
Claims queued: 4
Estimated serial runtime (min): 140

## Family Counts
- general_lrc_metric_pack: 1
- residue_error_pack: 2
- statistical_significance_pack: 1

## Tickets

| Ticket | Claim | Family | Runtime(min) | Acceptance Test |
|---|---|---|---:|---|
| MFIX-LRC-0001 | CLAIM-LRC-000032 | general_lrc_metric_pack | 25 | Metric recomputation matches recorded values within declared tolerance and units are consistent end-to-end. |
| MFIX-LRC-0002 | CLAIM-LRC-000049 | residue_error_pack | 40 | Recomputed max_error/avg_error differ by <=1e-12 relative and perfect_match classification is invariant across precisions. |
| MFIX-LRC-0003 | CLAIM-LRC-000050 | residue_error_pack | 40 | Recomputed max_error/avg_error differ by <=1e-12 relative and perfect_match classification is invariant across precisions. |
| MFIX-LRC-0004 | CLAIM-LRC-000051 | statistical_significance_pack | 35 | Recomputed p_value matches recorded p_value within 1e-12 and decision(alpha) is unchanged in float64/decimal128/mpmath. |
