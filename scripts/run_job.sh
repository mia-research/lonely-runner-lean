#!/bin/zsh
# run_job.sh — run a long computation safely.
#
#   scripts/run_job.sh <script.py> [args...]
#
# Guards, after the 2026-09-16 incident (two runs hung ten hours and wrote ~1 GB each):
#   * refuses a script read from stdin, and refuses a multiprocessing script with no __main__ guard
#     (a spawned worker cannot import a main module that came from stdin);
#   * kills the job if its CPU time stops advancing (STALL seconds, default 300) — the exact signature of that hang;
#   * kills it if the output file passes MAXOUT bytes (default 50 MB);
#   * kills it at WALL seconds (default 21600 = 6 h);
#   * prints why it stopped, with elapsed time and output size. (The stall detector reads process-group CPU
#     internally — a worker pool leaves the parent idle — but that reading is not carried out to the summary line.)
#
# Env: STALL, MAXOUT, WALL, OUT (output path; default <script>.out next to the script).
set -u
SCRIPT="${1:-}"
[[ -z "$SCRIPT" ]] && { print -u2 "usage: run_job.sh <script.py> [args...]"; exit 2 }
[[ "$SCRIPT" == "-" ]] && { print -u2 "refused: read the script from a file, not stdin"; exit 2 }
[[ -r "$SCRIPT" ]] || { print -u2 "refused: cannot read $SCRIPT"; exit 2 }
if grep -q "multiprocessing" "$SCRIPT" && ! grep -q "__main__" "$SCRIPT"; then
  print -u2 "refused: $SCRIPT uses multiprocessing without an if __name__ == '__main__' guard"; exit 2
fi
shift
STALL=${STALL:-300}; MAXOUT=${MAXOUT:-52428800}; WALL=${WALL:-21600}
OUT=${OUT:-"${SCRIPT%.py}.out"}
: > "$OUT"
python3 -u "$SCRIPT" "$@" > "$OUT" 2>&1 &
PID=$!
print "run_job: pid $PID, script $SCRIPT, output $OUT (stall ${STALL}s, max out ${MAXOUT}B, wall ${WALL}s)"
START=$(date +%s); LASTCPU=""; LASTMOVE=$START; REASON=""
CPUF=$(mktemp)                                  # the loop's last CPU reading, for the summary line
while kill -0 $PID 2>/dev/null; do
  sleep 5
  NOW=$(date +%s)
  PG=$(ps -o pgid= -p $PID 2>/dev/null | tr -d ' ')
  CPU=$(ps -Ao pgid=,time= 2>/dev/null | awk -v g="$PG" '$1==g {print $2}' | tr '\n' '+' )   # whole process group: a worker pool leaves the parent idle
  SIZE=$(wc -c < "$OUT" | tr -d ' ')
  print -r -- "$CPU" > "$CPUF"
  [[ "$CPU" != "$LASTCPU" ]] && { LASTCPU="$CPU"; LASTMOVE=$NOW }
  if (( NOW - LASTMOVE > STALL )); then REASON="stalled: no CPU progress for ${STALL}s"; break; fi
  if (( SIZE > MAXOUT )); then REASON="output passed ${MAXOUT} bytes"; break; fi
  if (( NOW - START > WALL )); then REASON="wall clock passed ${WALL}s"; break; fi
done
if [[ -n "$REASON" ]]; then
  kill -9 $PID 2>/dev/null; pkill -9 -P $PID 2>/dev/null
  print "run_job: KILLED — $REASON"
else
  wait $PID; RC=$?
  print "run_job: finished, exit $RC"
fi
END=$(date +%s)
rm -f "$CPUF"
print "run_job: elapsed $((END-START))s, output $(wc -c < "$OUT" | tr -d ' ') bytes"
tail -3 "$OUT"
