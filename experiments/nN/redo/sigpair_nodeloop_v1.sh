#!/bin/bash
# usage: sigpair_nodeloop_v1.sh LOGNAME "J o c part nparts" "J o c part nparts" ...   (each job repeated in <=540 s chunks until done)
cd "/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo"
LOG=sigpair_nodeloop_$1_v1.log; shift
for job in "$@"; do
  while true; do
    out=$(python3 sigpair_node_run_v1.py $job 540 2>&1 | tail -2)
    echo "$job :: $out" >> $LOG
    if echo "$out" | grep -q "todo 0"; then break; fi
    if echo "$out" | grep -q "this run 0 "; then break; fi
  done
done
echo ALLDONE >> $LOG
