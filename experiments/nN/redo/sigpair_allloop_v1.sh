#!/bin/bash
cd "/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo"
J=$1; P=$2; N=$3; LOG=sigpair_allloop_J${J}_p${P}_v1.log
while true; do
  out=$(python3 sigpair_allpairs_v1.py $J $P $N 540 2>&1 | tail -1); echo "$out" >> $LOG
  n=$(echo "$out" | sed -E 's/.*done: ([0-9]+) of ([0-9]+).*/\1 \2/'); set -- $J $P $N $n
  if [ "$4" == "$5" ]; then break; fi
done
echo ALLDONE >> $LOG
