#!/usr/bin/env bash
# Cascade artefact done-check gate (LonelyRunner/LRC/Cascade/).
#
# What PASS means: every module of the cascade artefact builds, contains no sorry / native_decide / unsafe /
# admit, and EVERY theorem in it depends on [propext, Classical.choice, Quot.sound] only.
#
# What PASS does NOT mean: Existence at order 8 -- that the cascade reaches a clear scale for every arrangement
# and runner -- is proved. It is open and deliberately not stated here; check [4] fails the gate if a declaration
# naming it appears.
#
# Checks: [0] build-artefact integrity (iCloud eviction); [1] explicit build of every module (a plain `lake build`
# does not enter LRC/); [2] sorry inventory; [2b] hygiene scan; [3] #print axioms on every theorem; [4] the open
# statement is not stated.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT" || exit 2
LOG="${1:-/tmp/cascade_gate_build.log}"
SRC=LonelyRunner/LRC/Cascade

# Progress timing. Every step prints its own elapsed time as it finishes, so a step running
# long is visible WHILE it runs rather than only in hindsight. Do not pipe this script through
# `tail`: tail holds the whole stream until exit, so the output reads empty for the full run
# whether the gate is healthy, hung or dead, and those become indistinguishable. Redirect to a
# file and read the tail of the file instead.
T0=$SECONDS; TSTEP=$SECONDS; PREV=""
step() {
  [ -n "$PREV" ] && echo "   ...$PREV took $((SECONDS-TSTEP))s"
  echo "== $* ==  (t+$((SECONDS-T0))s)"
  PREV="${1%% *}"; TSTEP=$SECONDS
}
# Measured baseline, WARM build, 2026-09-17, three runs: 13m12s / 12m20s / 12m04s.
# The last was instrumented: [0] 0s, [1] 46s, [2] 0s, [2b] 0s, [3] 678s, [4] 0s, total 724s.
# Step [3] is 93.6% of the run and scales with the theorem count (4688 here), so the total
# tracks it and this baseline drifts upward as the artefact grows. A COLD build makes step [1]
# much longer; there is no measured cold figure, so do not quote one.

step "[0] build-artefact integrity"
DATALESS=$(find .lake/build -name '*.olean' -print0 2>/dev/null \
  | xargs -0 stat -f '%b %N' 2>/dev/null | awk '$1==0 {print $2}')
if [ -n "$DATALESS" ]; then
  echo "  purging dataless (cloud-evicted) oleans:"
  echo "$DATALESS" | sed 's/^/    /'
  echo "$DATALESS" | while read -r f; do
    rm -f "$f" "${f%.olean}.trace" "${f%.olean}.olean.hash" "${f%.olean}.ilean" "${f%.olean}.ilean.hash"
  done
else
  echo "  clean"
fi

step "[1] build every cascade module"
# Derived from disk, not hardcoded: a hardcoded list goes stale silently, and on 2026-09-17 it was
# missing nine modules on disk (Certificate, EighthFamily, NearAP, CensusFamilies, CensusBatch,
# PinnedBatch1-4) while still claiming to build every one.
MODS=$(ls $SRC/*.lean | xargs -n1 basename | sed 's/\.lean$//' \
  | sed 's|^|LonelyRunner.LRC.Cascade.|' | tr '\n' ' ')
echo "  modules: $(echo $MODS | wc -w | tr -d ' ')"
lake build $MODS > "$LOG" 2>&1
BUILD_EXIT=$?
tail -1 "$LOG"
if [ $BUILD_EXIT -ne 0 ]; then
  echo "GATE FAIL: build exit $BUILD_EXIT"; grep -E 'error' "$LOG" | head -20; exit 1
fi

step "[2] sorry inventory"
SORRY=$(grep -nE '(^|[^[:alnum:]_])sorry([^[:alnum:]_]|$)' $SRC/*.lean 2>/dev/null \
  | grep -vE ':[0-9]+: *--' | grep -vE '`sorry`')
if [ -n "$SORRY" ]; then echo "$SORRY" | sed 's/^/  /'; else echo "  none"; fi

step "[2b] proof-hygiene scan"
HYG=$(grep -rnE 'native_decide|^[[:space:]]*unsafe[[:space:]]+(def|theorem|lemma|instance)|(^|<;>[[:space:]]*|;[[:space:]]*)[[:space:]]*admit[[:space:]]*$' \
  $SRC/*.lean 2>/dev/null | grep -vE '^[^:]+:[0-9]+:[[:space:]]*--' | grep -vE '`native_decide`|`unsafe`|`admit`')
if [ -n "$HYG" ]; then echo "$HYG" | sed 's/^/  /'; HYG_OK=0; else echo "  clean"; HYG_OK=1; fi

step "[3] axiom check, every theorem"
AX=LonelyRunner/_CascadeGateAxCheck.lean
{
  echo 'import LonelyRunner.LRC.Cascade.All'
  for f in $(ls $SRC/*.lean | grep -v '/All.lean$'); do   # every module, so a new file cannot be missed
    awk '/^namespace /{ns=$2} /^end /{if($2==ns) ns=""} \
         /^[[:space:]]*(private |protected )*(theorem|lemma) /{ \
           for(i=1;i<=NF;i++) if($i=="theorem"||$i=="lemma"){name=$(i+1); break} \
           if(ns!="") print "#print axioms " ns "." name; else print "#print axioms " name}' "$f"
  done
} > "$AX"
NDECL=$(grep -c '^#print axioms' "$AX")
# Coverage assertion: silent under-extraction would report "N of N clean" while checking fewer than
# exist. Compare against an independent count of proof-carrying declarations on disk.
# Deliberately BROADER than the extractor's own pattern -- attribute prefixes, `nonrec`, `noncomputable`
# -- so a declaration written in a form the extractor cannot name makes the counts differ instead of
# being skipped silently. A same-pattern count on both sides would agree by construction and never fire.
NDISK=$(grep -hcE '^[[:space:]]*(@\[[^]]*\][[:space:]]*)*(private |protected |nonrec |noncomputable )*(theorem|lemma)[[:space:]]' \
  $(ls $SRC/*.lean | grep -v '/All.lean$') 2>/dev/null | awk '{s+=$1} END{print s+0}')
if [ "$NDECL" != "$NDISK" ]; then
  echo "  COVERAGE FAIL: extracted $NDECL, but $NDISK proof-carrying declarations are on disk"
  echo "  (a declaration the extractor misses is never axiom-checked)"
  COV_OK=0
else
  COV_OK=1
fi
AXOUT=$(lake env lean "$AX" 2>&1)
rm -f "$AX"
NCLEAN=$(echo "$AXOUT" | grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]")
echo "  $NCLEAN of $NDECL clean"
BAD=$(echo "$AXOUT" | grep -vE "depends on axioms: \[propext, Classical.choice, Quot.sound\]" | grep -E "axiom|error|sorryAx|unknown")
if [ -n "$BAD" ]; then echo "$BAD" | sed 's/^/  /'; fi
[ "$NCLEAN" = "$NDECL" ] && AX_OK=1 || AX_OK=0

step "[4] the open statement (Existence at order 8) must NOT be stated"
# A NAME TRIPWIRE, not a proof of absence: it catches a declaration named for the open statement, and
# would not catch one proved under an unrelated name. The frozen statement itself lives in
# LonelyRunner/LRC/Spec/Target.lean, deliberately outside this artefact.
OPEN=$(grep -nE '^[[:space:]]*(theorem|lemma|def|axiom)[[:space:]]+[A-Za-z_.]*([Ll][Rr][Cc]|[Cc]laim|[Ee]xistence|ExistenceAt8|reaches_clear_scale|run_always_ends)' \
  $SRC/*.lean 2>/dev/null)
if [ -n "$OPEN" ]; then echo "$OPEN" | sed 's/^/  /'; OPEN_OK=0; else echo "  clean (unstated, as intended)"; OPEN_OK=1; fi

[ -n "$PREV" ] && echo "   ...$PREV took $((SECONDS-TSTEP))s"
echo "== total: $((SECONDS-T0))s =="
echo
if [ "$AX_OK" = "1" ] && [ "$COV_OK" = "1" ] && [ -z "$SORRY" ] && [ "$HYG_OK" = "1" ] && [ "$OPEN_OK" = "1" ]; then
  echo "GATE PASS: $NDECL theorems, axiom-clean (coverage $NDECL of $NDISK on disk)."
  echo "           Existence at order 8 is NOT proved -- it remains open and unstated."
  exit 0
fi
echo "GATE FAIL."; exit 1
