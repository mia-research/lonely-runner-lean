#!/bin/bash
# Compile Fresh/M4ZoneChunks/G_*.lean (P in parallel), then Fresh/M4ZoneFinal.lean.
# Per-file results: experiments/n8/zone_m4_lean_v1.tsv (file, rc, seconds); logs in zone_lean_logs/.
P=${1:-4}
S=/private/tmp/claude-501/-Users-trentpalelei-Desktop-Math-Ex/4fa96dd3-a370-480d-8f4e-06aff9315a98/scratchpad
cd "/Users/trentpalelei/Desktop/Math Ex/LonelyRunnerFresh" || exit 1
. $S/lp.sh; export LEAN_PATH
mkdir -p build/Fresh/M4ZoneChunks ../experiments/n8/zone_lean_logs
OUT=../experiments/n8/zone_m4_lean_v1.tsv
# largest files first
ls -S Fresh/M4ZoneChunks/G_*.lean | xargs -P "$P" -I{} bash -c 'm=$(basename {} .lean); s=$(date +%s); lean {} -R . -o build/Fresh/M4ZoneChunks/$m.olean > ../experiments/n8/zone_lean_logs/m4_$m.log 2>&1; echo -e "$m\t$?\t$(( $(date +%s)-s ))"' >> $OUT
s=$(date +%s); lean Fresh/M4ZoneFinal.lean -R . -o build/Fresh/M4ZoneFinal.olean > ../experiments/n8/zone_lean_logs/m4_final.log 2>&1
echo -e "FINAL\t$?\t$(( $(date +%s)-s ))" >> $OUT
