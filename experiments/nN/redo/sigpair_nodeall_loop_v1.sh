#!/bin/bash
cd "/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo"
J=$1; P=$2; N=$3; LOG=sigpair_nodeall_loop_J${J}_p${P}_v1.log
while true; do
  out=$(python3 sigpair_nodeall_run_v1.py $J $P $N 540 2>&1 | tail -2); echo "$out" >> $LOG
  if echo "$out" | grep -q "todo 0"; then break; fi
done
echo ALLDONE >> $LOG
