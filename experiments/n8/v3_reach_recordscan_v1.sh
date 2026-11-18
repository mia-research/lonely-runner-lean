#!/bin/bash
# Shown scan: any earlier use of the reach of a W_0 chain on the V3 region, the value 4257/833 or 231/47, or a landing bound for rho6 > 17.
cd "/Users/trentpalelei/Desktop/Math Ex"
for pat in '4257/833' '231/47' '1863081/394289' 'reach of a table' 'reach.*V3' 'V3.*reach'; do
  echo "== $pat"; grep -rIl -- "$pat" docs/n8 experiments/n8 LonelyRunnerFresh/Fresh --include=*.md --include=*.py --include=*.out --include=*.sh --include=*.lean 2>/dev/null | grep -v 'v3_reach_' 
done
echo "== E873-E876 entries (headings)"; grep -nE '^## E87[3-6]' docs/n8/RUNNING_LOG_order8_v1.md | cut -c1-140
