# Audit Rules

Notation checks:
1. Detect mixed symbol families without mapping, e.g. `phi` vs `varphi`.
2. Detect overloaded uses of the same symbol in one claim text.
3. Flag missing definition markers near symbols.

Measurement checks:
1. Compare claim metric terms against experiment metric terms.
2. Flag mismatches such as testing `global isolation` but claiming `individual isolation`.
3. Mark unknown when input lacks metric text.

Output labels:
- `metric_match`: `pass|fail|partial`
- `notation_match`: `pass|fail|partial`
- `numeric_escalation`: `yes|no`
