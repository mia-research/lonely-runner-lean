#!/bin/bash
# Shown scan: does anything in docs/n8, experiments/n8 or the Lean trees already treat the chain-cover search growth / a jump in B, or the chain object?
cd "/Users/trentpalelei/Desktop/Math Ex"
for pat in 'chain_cover' 'ChainBox' 'chain cover' 'irredund' 'carve of' 'NoCarve' 'search size' 'node count' 'nodes by depth' ; do
  echo "== docs/n8+experiments/n8 : $pat"; grep -rIil -- "$pat" docs/n8 experiments/n8 --include=*.md --include=*.py --include=*.out --include=*.sh 2>/dev/null | head -25
  echo "== Lean trees : $pat"; grep -rIil -- "$pat" LonelyRunnerFresh/Fresh LonelyRunner --include=*.lean 2>/dev/null | head -15
done
