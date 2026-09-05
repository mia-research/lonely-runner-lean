# Budget Policy

Default thresholds:
1. `manager_cap_ratio = 0.15`
2. `premium_cap_ratio = 0.35`
3. `provider_quota_warning_ratio = 0.80`

Cycle health:
1. `green`: all thresholds satisfied
2. `amber`: warning threshold crossed with reroute action
3. `red`: unresolved governance breach or hard cap violation

Recommended remediation:
1. Re-route non-critical tasks to cheaper workers.
2. Defer high-impact adjudication if premium providers are constrained.
3. Reduce batch size for next cycle.
