#!/bin/sh
cd "$(dirname "$0")"
for spec in "1 40" "2 44" "3 45"; do
  set -- $spec
  while :; do
    python3 lat_enum2_v1.py $1 $2 540 >> lat_enum2_log_v1.out 2>&1
    tail -1 lat_enum2_log_v1.out | grep -q "doneM $2 target" && break
  done
done
echo CHAIN_DONE >> lat_enum2_log_v1.out
