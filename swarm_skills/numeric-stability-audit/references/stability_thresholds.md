# Stability Thresholds

Default thresholds:
1. `stable`: max relative diff <= 1e-9
2. `precision_sensitive`: 1e-9 < max relative diff <= 1e-5
3. `unstable`: max relative diff > 1e-5

Required report fields:
1. key/path
2. baseline value
3. high-precision value
4. absolute diff
5. relative diff
6. row-level status
7. global status

Policy:
- Any global status other than `stable` blocks A-level promotion.
