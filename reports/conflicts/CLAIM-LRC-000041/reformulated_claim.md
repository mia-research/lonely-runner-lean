# CLAIM-LRC-000041 Reformulated Claim

## Operational Proposition (Empirical, Falsifiable)
For dataset `lrc_individual_isolation_1759267335152.csv`, restricted to rows with:
- `family = arithmetic`, `n = 6`, `horizon = 1000`,

the following hold:
1. `complete_success = YES` in all observed rows (100/100).
2. `runners_isolated = 6` in all observed arithmetic rows.
3. `avg_first_isolation` remains tightly concentrated near `5/3` (observed range: 1.666666666666643 to 1.666666666666665).

Contrast set in the same file:
- For `family = random`, `n = 6`, `horizon = 1000`, complete isolation is not universal (98/100 complete; 2 failures).
- Non-complete seeds observed: 506060, 506091.

## Boundary Conditions
- Arithmetic boundary_count range: 3601 to 6001
- Random boundary_count range: 6918 to 24413

## Falsification Rule
This reformulated claim is rejected if any arithmetic row in the stated slice has:
- `complete_success != YES`, or
- `runners_isolated != 6`, or
- `avg_first_isolation` materially outside the observed concentration around `5/3`.
