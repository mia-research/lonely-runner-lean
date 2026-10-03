#!/bin/bash
# usage: sigpair_scanloop_v1.sh LOG "o c" "o c" ...
cd "/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo"
LOG=sigpair_scanloop_$1_v1.log; shift
for job in "$@"; do
  set -- $job
  while true; do
    out=$(python3 sigpair_scan_v1.py 2 $1 $2 1 540 2>&1 | tail -2); echo "$job :: $out" >> $LOG
    if echo "$out" | grep -q "todo 0"; then break; fi
    if echo "$out" | grep -q "FEAS after"; then break; fi
    if echo "$out" | grep -q "witness already"; then break; fi
  done
done
echo ALLDONE >> $LOG
