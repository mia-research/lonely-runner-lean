#!/bin/zsh
# Slabs S in [B-1, B], B = 13 .. 24, every climb followed through band 1 (climb_cells_v3, bands = 2).
# Each slab is a result on its own.  A climb leaving band 1 is written to <tag>.TERMINALS.txt at once.
for B in 13 14 15 16 17 18 19 20 21 22 23 24; do
  L=$((B-1))
  echo "=== S in [$L, $B] start $(date '+%H:%M:%S')"
  python3 climb_cells_v3.py $B $L 2 > climb_cells_v3_B${B}_S${L}_bands2.out 2>&1
  grep -E "explored|terminal cells|far reading" climb_cells_v3_B${B}_S${L}_bands2.out
  if [ -s climb_cells_v3_B${B}_S${L}_bands2.TERMINALS.txt ]; then echo "!!! EXITS FROM BAND 1 FOUND in S in [$L, $B]"; fi
  echo "=== S in [$L, $B] end $(date '+%H:%M:%S')"
done
