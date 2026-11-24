#!/bin/bash
# v2: compile Fresh/M4ZoneChunks/C/C_*.lean (P in parallel, largest first), then G_*.lean,
# then Fresh/M4ZoneFinal.lean, then Fresh/BandAssemblyReduced.lean.
# Rows (stage, file, rc, seconds, maxRSS bytes) in experiments/n8/zone_m4_lean_v2.tsv; logs in zone_lean_logs/.
P=${1:-3}
S=/private/tmp/claude-501/-Users-trentpalelei-Desktop-Math-Ex/4fa96dd3-a370-480d-8f4e-06aff9315a98/scratchpad
cd "/Users/trentpalelei/Desktop/Math Ex/LonelyRunnerFresh" || exit 1
. $S/lp.sh; export LEAN_PATH
mkdir -p build/Fresh/M4ZoneChunks/C ../experiments/n8/zone_lean_logs
OUT=../experiments/n8/zone_m4_lean_v2.tsv
one() {  # stage srcfile
  f=$2; m=${f#Fresh/}; m=${m%.lean}; lg=../experiments/n8/zone_lean_logs/m4v2_$(echo $m | tr / _).log
  if [ "$SKIP_BUILT" = 1 ] && [ -s build/$m.olean ] && [ build/$m.olean -nt $f ]; then echo -e "$1\t$m\t0\t0\tcached"; return; fi
  s=$(date +%s); /usr/bin/time -l lean $f -R . -o build/$m.olean > $lg 2>&1; rc=$?
  echo -e "$1\t$m\t$rc\t$(( $(date +%s)-s ))\t$(awk '/maximum resident/{print $1}' $lg)"
}
export -f one
ls -S Fresh/M4ZoneChunks/C/C_*.lean | xargs -P "$P" -I{} bash -c 'one C {}' >> $OUT
ls -S Fresh/M4ZoneChunks/G_*.lean | xargs -P "$P" -I{} bash -c 'one G {}' >> $OUT
one FINAL Fresh/M4ZoneFinal.lean >> $OUT
one REDUCED Fresh/BandAssemblyReduced.lean >> $OUT
echo done
