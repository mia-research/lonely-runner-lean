#!/bin/bash
# E124: wall-cut covers of spread strips [a, a+1] up to 24, each generated then independently checked.
cd "$(dirname "$0")"
for a in $(seq 10 23); do
  b=$((a+1))
  SLO=$a SHI=$b python3 strip_cover_gen_v1.py > strip_cover_${a}_${b}.out 2>&1
  echo "strip [$a,$b]: $(tail -1 strip_cover_${a}_${b}.out)" >> strips_progress_v1.txt
  python3 strip_cover_check_v1.py strip_cover_tree_${a}_${b}.json $a $b | tail -1 >> strips_progress_v1.txt
done
echo ALLDONE >> strips_progress_v1.txt
