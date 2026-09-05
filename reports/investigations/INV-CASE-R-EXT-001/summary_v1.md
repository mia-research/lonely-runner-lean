# INV-CASE-R-EXT-001: Extended Case R> Investigation — Summary

**Total configs tested:** 9163  |  **Successes:** 9163 (100.00%)  |  **Failures:** 0

## ILE Level Distribution

| Levels L | Count | % |
|---|---|---|
| 0 | 2259 | 24.7% |
| 1 | 2743 | 29.9% |
| 2-5 | 3923 | 42.8% |
| 6-10 | 228 | 2.5% |
| 11-20 | 10 | 0.1% |
| 21-50 | 0 | 0.0% |
| >50 | 0 | 0.0% |

**Max L observed:** 20  |  **Mean L (successes):** 1.71

## Containment Margin Distribution (min W_hi − t_cur, as % of |W₀|)

| Margin % of |W₀| | Count | % |
|---|---|---|
| <1% | 0 | 0.0% |
| 1-5% | 0 | 0.0% |
| 5-10% | 0 | 0.0% |
| 10-25% | 0 | 0.0% |
| 25-50% | 0 | 0.0% |
| >=50% | 9163 | 100.0% |

**Min containment margin:** 54.5455% of |W₀|
**Median:** 99.7465%

## Step L2 Buffer Distribution

- **Min buffer:** -578.545455  (negative ⟹ Step L2 violated)
- **Median buffer:** -0.210227
- **Buffers < 0:** 2572
- **Buffers < 1:** 3029

## Carry Event Totals

- Total carry events: 12544
- Type C (cross upper boundary): 8372 (66.7%)
- Type W (wrap past integer): 4172 (33.3%)

## Results by Config Type

| Type | N | Success | Max L | Min Margin |
|---|---|---|---|---|
| A | 9000 | 9000/9000 | 20 | 0.0598 |
| B-adversarial_variant | 1 | 1/1 | 9 | 0.7374 |
| B-consec-R100 | 3 | 3/3 | 0 | 0.2727 |
| B-consec-R1000 | 3 | 3/3 | 0 | 0.2727 |
| B-consec-R11 | 3 | 3/3 | 1 | 0.2700 |
| B-consec-R12 | 3 | 3/3 | 0 | 0.2727 |
| B-consec-R15 | 3 | 3/3 | 0 | 0.2727 |
| B-consec-R20 | 3 | 3/3 | 0 | 0.2727 |
| B-consec-R50 | 3 | 3/3 | 0 | 0.2727 |
| B-consec-R500 | 3 | 3/3 | 0 | 0.2727 |
| B-paper_example | 1 | 1/1 | 5 | 0.7532 |
| B-resonant | 20 | 20/20 | 5 | 0.0364 |
| C-odd-ratio1001 | 1 | 1/1 | 1 | 0.8099 |
| C-odd-ratio101 | 1 | 1/1 | 2 | 0.8092 |
| C-odd-ratio19 | 1 | 1/1 | 1 | 0.8099 |
| C-odd-ratio21 | 1 | 1/1 | 2 | 0.8095 |
| C-odd-ratio501 | 1 | 1/1 | 1 | 0.8099 |
| C-odd-ratio51 | 1 | 1/1 | 2 | 0.8093 |
| C-p11-R100 | 1 | 1/1 | 0 | 0.8182 |
| C-p11-R1000 | 1 | 1/1 | 0 | 0.8182 |
| C-p11-R11 | 1 | 1/1 | 1 | 0.8099 |
| C-p12-R100 | 1 | 1/1 | 0 | 0.4091 |
| C-p12-R1000 | 1 | 1/1 | 0 | 0.4091 |
| C-p12-R11 | 1 | 1/1 | 1 | 0.4050 |
| C-p13-R100 | 1 | 1/1 | 0 | 0.2727 |
| C-p13-R1000 | 1 | 1/1 | 0 | 0.2727 |
| C-p13-R11 | 1 | 1/1 | 1 | 0.2700 |
| C-ratio100 | 1 | 1/1 | 0 | 0.8182 |
| C-ratio1000 | 1 | 1/1 | 0 | 0.8182 |
| C-ratio11 | 1 | 1/1 | 1 | 0.8099 |
| C-ratio12 | 1 | 1/1 | 0 | 0.8182 |
| C-ratio15 | 1 | 1/1 | 0 | 0.8182 |
| C-ratio20 | 1 | 1/1 | 0 | 0.8182 |
| C-ratio200 | 1 | 1/1 | 0 | 0.8182 |
| C-ratio50 | 1 | 1/1 | 0 | 0.8182 |
| C-ratio500 | 1 | 1/1 | 0 | 0.8182 |
| P-k2 | 20 | 20/20 | 12 | 0.6713 |
| P-k2-consec | 1 | 1/1 | 1 | 0.8140 |
| P-k3 | 20 | 20/20 | 6 | 0.7686 |
| P-k3-consec | 1 | 1/1 | 1 | 0.8154 |
| P-k4 | 20 | 20/20 | 5 | 0.7879 |
| P-k4-consec | 1 | 1/1 | 1 | 0.8161 |
| P-k5 | 20 | 20/20 | 5 | 0.7873 |
| P-k5-consec | 1 | 1/1 | 1 | 0.8165 |
| P-ratio11-miss10 | 1 | 1/1 | 1 | 0.8099 |
| P-ratio11-miss2 | 1 | 1/1 | 20 | 0.4463 |
| P-ratio11-miss3 | 1 | 1/1 | 13 | 0.6000 |
| P-ratio11-miss4 | 1 | 1/1 | 9 | 0.6768 |
| P-ratio11-miss5 | 1 | 1/1 | 7 | 0.7190 |
| P-ratio11-miss6 | 1 | 1/1 | 5 | 0.7532 |
| P-ratio11-miss7 | 1 | 1/1 | 4 | 0.7727 |
| P-ratio11-miss8 | 1 | 1/1 | 3 | 0.7879 |
| P-ratio11-miss9 | 1 | 1/1 | 2 | 0.8000 |
