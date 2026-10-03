#!/bin/bash
# repeated chunks (each < 10 min) until all cells of window J are done
cd "/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo"
J=$1
while true; do
  out=$(WORKERS=1 python3 sigpair_run_v1.py $J 540 2>&1 | tail -2)
  echo "$out" >> sigpair_loop_J${J}_v1.log
  if echo "$out" | grep -q "todo 0"; then break; fi
  if echo "$out" | grep -q "finished this run: 0 "; then break; fi
done
echo ALLDONE >> sigpair_loop_J${J}_v1.log
