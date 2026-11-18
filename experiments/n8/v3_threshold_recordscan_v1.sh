#!/bin/bash
# Shown scan: does the record already contain the anchor-extension thresholds 713/25, 403/11 (= (8j+7)(8j-1)/(8j+1) for j = 3, 4) or the formula?
cd "/Users/trentpalelei/Desktop/Math Ex"
for pat in '713/25' '403/11' '28\.52' '(8j+7)(8j-1)' '(8j+7)\*(8j-1)'; do
  echo "== $pat"; grep -rIl -- "$pat" docs/n8 experiments/n8 LonelyRunnerFresh/Fresh --include=*.md --include=*.py --include=*.out --include=*.sh --include=*.lean 2>/dev/null
done
