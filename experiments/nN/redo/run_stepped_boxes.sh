#!/bin/zsh
# Stepped certificates for far reading S in [9, B], B = 10 .. 17 (climb_cells_v2).  Each box is a result on its own;
# a climb into (7,9) is written to <tag>.TERMINALS.txt the moment it is found.  Run under caffeinate.
for B in 10 11 12 13 14 15 16 17; do
  echo "=== B=$B start $(date '+%H:%M:%S')"
  python3 climb_cells_v2.py $B 9 > climb_cells_v2_B${B}_S9.out 2>&1
  cat climb_cells_v2_B${B}_S9.out
  echo "=== B=$B end $(date '+%H:%M:%S')"
done
