#!/usr/bin/env bash
# Spec-layer done-check gate  (LonelyRunner/LRC/Spec/).
#
# WHY THIS EXISTS.  Until 2026-09-21 NOTHING in LRC/Spec/ was gated.  The exemption was written
# for Target.lean and Doors.lean, so that the cascade gate's check [4] -- "the open statement is
# not stated" -- would keep its meaning with the target living somewhere.  The general-n layer
# (DoorsN, FlankFiniteN, ResonanceN, WindowN, SelfSimilarN, OtherFlankN, IrrationalN) was then
# written behind that exemption without anyone asking whether it still applied.  It did not.
# The audit that stood in for a gate, experiments/n8/full_audit_v3.lean, was a HAND-MAINTAINED
# list of #print axioms: it had no coverage assertion, and it was missing 7 of the 146
# declarations on disk without saying so.  That is the exact defect the cascade gate's coverage
# assertion was added for after the 4,749/4,748 count.
#
# What PASS means: every Spec module builds; no sorry, native_decide, unsafe or admit; EVERY
# declaration on disk is axiom-checked and within [propext, Classical.choice, Quot.sound]; and
# every `def ... : Prop` is on the OWED register below with a recorded standing.
#
# What PASS does NOT mean: LRC is proved at any order.  Spec/ is where the TARGET is stated, so
# this gate deliberately does NOT carry the cascade gate's name tripwire.  Its analogue here is
# check [4]: a Prop that is ASSERTED and concluded by no theorem is invisible to a build, to a
# sorry scan and to #print axioms -- that is how DoorFirstLap survived two days as a false
# statement -- so every one of them is registered by hand and a NEW one fails the gate.
#
# Checks: [0] build-artefact integrity (iCloud eviction); [1] build every module, list from disk;
# [2] sorry; [2b] hygiene; [3] #print axioms on every declaration + coverage assertion;
# [4] the OWED register of asserted Props; [5] tree fingerprint start/end.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT" || exit 2
LOG="${1:-/tmp/spec_gate_build.log}"
SRC=LonelyRunner/LRC/Spec

T0=$SECONDS; TSTEP=$SECONDS; PREV=""
step() {
  [ -n "$PREV" ] && echo "   ...$PREV took $((SECONDS-TSTEP))s"
  echo "== $* ==  (t+$((SECONDS-T0))s)"
  PREV="${1%% *}"; TSTEP=$SECONDS
}
# Not atomic against edits: fingerprint the tree at both ends, as the cascade gate does.
TREE_AT_START=$(cd "$SRC" && shasum -a 256 *.lean | sort -k2 | shasum -a 256 | cut -d' ' -f1)

# ---- the declaration extractor -------------------------------------------------------------
# Namespace-aware and comment-stripped.  Emits "<kind> <fully.qualified.name>" per declaration.
# Kept in one place so checks [3] and [4] cannot disagree about what a declaration is.
extract() {
python3 - "$@" <<'PYEOF'
import re, sys
for path in sys.argv[1:]:
    src = open(path).read()
    src = re.sub(r'/-.*?-/', '', src, flags=re.S)          # block and doc comments
    ns = []
    for line in src.split('\n'):
        line = re.sub(r'--.*$', '', line)
        m = re.match(r'\s*namespace\s+([A-Za-z_][\w.\x27]*)', line)
        if m: ns.append(m.group(1)); continue
        m = re.match(r'\s*end\s+([A-Za-z_][\w.\x27]*)\s*$', line)
        if m:
            if ns and ns[-1] == m.group(1): ns.pop()
            continue
        m = re.match(r'\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*'
                     r'(theorem|lemma|def|abbrev|instance)\s+([A-Za-z_][\w.\x27!?]*)', line)
        if m:
            kind, name = m.group(1), m.group(2)
            print(f"{kind} {'.'.join(ns + [name])}")
PYEOF
}

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

step "[1] build every Spec module (list derived from disk)"
# From disk, never hardcoded: a fixed list goes stale silently and on 2026-09-17 the cascade
# gate's was found missing nine modules while still claiming to build every one.
MODS=$(ls $SRC/*.lean | xargs -n1 basename | sed 's/\.lean$//' \
       | sed 's|^|LonelyRunner.LRC.Spec.|' | tr '\n' ' ')
echo "  $(echo $MODS | wc -w | tr -d ' ') modules"
lake build $MODS > "$LOG" 2>&1
BUILD_EXIT=$?
tail -2 "$LOG"
if [ $BUILD_EXIT -ne 0 ]; then
  echo "GATE FAIL: build exit $BUILD_EXIT"; grep -E 'error' "$LOG" | head -20; exit 1
fi

step "[2] sorry inventory"
SORRY=$(grep -nE '(^|[^[:alnum:]_])sorry([^[:alnum:]_]|$)' $SRC/*.lean 2>/dev/null \
  | grep -vE ':[0-9]+: *--' | grep -vE '`sorry`')
if [ -n "$SORRY" ]; then echo "$SORRY" | sed 's/^/  /'; else echo "  none"; fi

step "[2b] proof-hygiene scan"
# `axiom` is in this scan because check [3] catches a declaration that USES a planted axiom but
# would not name the axiom itself.  Spec/ states Props; it declares no axioms.
HYG=$(grep -rnE '^[[:space:]]*axiom[[:space:]]|native_decide|^[[:space:]]*unsafe[[:space:]]+(def|theorem|lemma|instance)|(^|<;>[[:space:]]*|;[[:space:]]*)[[:space:]]*admit[[:space:]]*$' \
  $SRC/*.lean 2>/dev/null | grep -vE '^[^:]+:[0-9]+:[[:space:]]*--' \
  | grep -vE '`native_decide`|`unsafe`|`admit`|`axiom`')
if [ -n "$HYG" ]; then echo "$HYG" | sed 's/^/  /'; HYG_OK=0
else echo "  clean (no axiom / native_decide / unsafe / admit)"; HYG_OK=1; fi

step "[3] axiom check on EVERY declaration, with a coverage assertion"
extract $SRC/*.lean | sort -u > /tmp/spec_gate_decls.txt
NDECL=$(wc -l < /tmp/spec_gate_decls.txt | tr -d ' ')
# The coverage assertion.  An INDEPENDENT count, with a deliberately broader pattern, over the
# same comment-stripped source.  If the extractor cannot name a declaration that is on disk,
# the gate fails rather than skipping it silently.  This is the check full_audit_v3 lacked.
NDISK=$(python3 - $SRC/*.lean <<'PYEOF'
import re, sys
n = 0
for path in sys.argv[1:]:
    src = re.sub(r'/-.*?-/', '', open(path).read(), flags=re.S)
    for line in src.split('\n'):
        line = re.sub(r'--.*$', '', line)
        if re.match(r'\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*'
                    r'(theorem|lemma|def|abbrev|instance)\s', line):
            n += 1
print(n)
PYEOF
)
# An ANONYMOUS instance (`instance : Fact (2 <= 5) := ...`) has no name, so #print axioms cannot
# be run on it.  That is a real exclusion and it is counted and printed, not absorbed: named +
# anonymous must equal the broad count, or the gate fails.
# anonymous = `instance` NOT followed by a name: `instance :`, `instance (x : T) :`, ...
NANON=$(grep -cE '^[[:space:]]*instance[[:space:]]*([:({[]|$)' $SRC/*.lean | awk -F: '{s+=$2} END {print s+0}')
echo "  extractor names $NDECL; $NANON anonymous instance(s) unnameable; $NDISK on disk"
if [ "$((NDECL+NANON))" != "$NDISK" ]; then
  echo "  COVERAGE FAIL: $((NDISK-NDECL-NANON)) declaration(s) on disk the extractor cannot name"
  echo "  and cannot explain.  Fix the extractor -- do NOT lower the count."
  COV_OK=0
else
  COV_OK=1
fi
AX=LonelyRunner/_SpecGateAxCheck.lean
{
  for m in $MODS; do echo "import $m"; done
  awk '{print "#print axioms " $2}' /tmp/spec_gate_decls.txt
} > "$AX"
# Lean wraps a long `depends on axioms: [...]` list over several lines (a long declaration name
# pushes it past the width); rejoin continuation lines, which start with a space, before matching.
AXOUT=$(lake env lean "$AX" 2>&1 | awk 'NR>1 && /^ / {printf "%s", $0; next} NR>1 {print ""} {printf "%s", $0} END {print ""}')
rm -f "$AX"
ALLOWED='depends on axioms: \[(propext)?(, )?(Classical\.choice)?(, )?(Quot\.sound)?\]$'
NCLEAN=$(echo "$AXOUT" | grep -cE "$ALLOWED")
NFREE=$(echo "$AXOUT" | grep -c "does not depend on any axioms")
echo "  $((NCLEAN+NFREE)) of $NDECL clean ($NFREE depend on no axioms at all)"
BAD=$(echo "$AXOUT" | grep -vE "$ALLOWED" | grep -vE "does not depend on any axioms" \
      | grep -E "axiom|error|sorryAx")
if [ -n "$BAD" ]; then echo "$BAD" | sed 's/^/  /'; fi
[ "$((NCLEAN+NFREE))" = "$NDECL" ] && AX_OK=1 || AX_OK=0
echo "$AXOUT" | grep -q "sorryAx" && AX_OK=0

step "[4] the OWED register: every asserted Prop is accounted for"
# WHY THIS EXISTS.  `def Foo : Prop := ...` is TYPE-CHECKED, never proved.  A false one compiles,
# carries no sorry, and reports clean under #print axioms.  DoorFirstLap was exactly that for two
# days and was found by reading, not by any gate.  So every Prop-valued def in Spec/ is listed
# here with its standing, and an unregistered one fails the gate.  Adding a name to this list is
# a deliberate act that says: I have decided what this Prop's standing is.
#
#   TARGET   the conjecture or an Iff.rfl restatement of it -- stated on purpose
#   ROUTE    proved equivalent to, or sufficient for, the target by a theorem in the tree
#   OWED     asserted, NOT proved, appears only as an explicit hypothesis
#   REFUTED  known false; retained with nothing resting on it
REGISTER="
LRC.Spec.ExistenceAt8:ROUTE           LRC.Spec.ExistenceAt8_cascade:ROUTE
LRC.Spec.ExistenceAt8_flank:ROUTE     LRC.Spec.ExistenceAt8_congruence:ROUTE
LRC.Spec.ExistenceOnArrangements:TARGET LRC.Spec.LonelyRunnerAt8:TARGET
LRC.Spec.CascadeCapped:ROUTE          LRC.Spec.FiniteActiveMembership:ROUTE
LRC.Spec.ThreeLargestFlanks:ROUTE     LRC.Spec.LonelyForSubject:ROUTE
LRC.Spec.LonelyAt:ROUTE               LRC.Spec.InWay:ROUTE
LRC.Spec.DoorFlank:ROUTE              LRC.Spec.DoorArrives:ROUTE
LRC.Spec.DoorCapped:ROUTE             LRC.Spec.DoorFAM:ROUTE
LRC.Spec.DoorThreeLargest:ROUTE       LRC.Spec.DoorTwoLargest:ROUTE
LRC.Spec.DoorFirstLap:REFUTED         LRC.Spec.DoorLargestFlank:REFUTED
LRC.SpecN.ExistenceAtN:ROUTE          LRC.SpecN.ExistenceAtN_cascade:ROUTE
LRC.SpecN.ExistenceAtN_flank:ROUTE    LRC.SpecN.ExistenceAtN_congruence:ROUTE
LRC.SpecN.ExistenceOnArrangements:TARGET LRC.SpecN.LonelyRunnerAtN:TARGET
LRC.SpecN.CascadeCapped:ROUTE         LRC.SpecN.FiniteActiveMembership:ROUTE
LRC.SpecN.ThreeLargestFlanks:ROUTE    LRC.SpecN.LonelyForSubject:ROUTE
LRC.SpecN.LonelyAt:ROUTE              LRC.SpecN.InWay:ROUTE
LRC.SpecN.DoorFlank:ROUTE             LRC.SpecN.DoorArrives:ROUTE
LRC.SpecN.DoorCapped:ROUTE            LRC.SpecN.DoorFAM:ROUTE
LRC.SpecN.DoorThreeLargest:ROUTE      LRC.SpecN.DoorTwoLargest:ROUTE
LRC.SpecN.DoorFirstLap:REFUTED        LRC.SpecN.DoorLargestFlank:REFUTED
LRC.FlankFinite.FourClears:OWED       LRC.Resonance.CoprimeLargestFlank:OWED
LRC.OrderFive.RCapped:OWED            LRC.OrderFive.WindowConstantFive:OWED
LRC.Order8Skeleton.BlockRule8:ROUTE   LRC.Order8Skeleton.Arr8:ROUTE
LRC.Order8Skeleton.ArrBlockRule8:OWED LRC.Order8Skeleton.ArrBoundedCovered8:OWED
LRC.Order8Skeleton.Lonely8:ROUTE      LRC.Order8Skeleton.Separated8:ROUTE
LRC.RationalN.ratWorks:ROUTE          LRC.OrderFive.BandFits:ROUTE
LRC.Resonance.Resonant:ROUTE          LRC.Resonance.GoodK:ROUTE
LRC.OrderSevenN.avoids06:ROUTE        LRC.OrderSevenN.fitsWindow5:ROUTE
LRC.OrderSevenN.fits4:ROUTE           LRC.OrderSevenN.fits3:ROUTE
LRC.OrderSevenN.fits2:ROUTE           LRC.OrderSevenN.intervalAvoids:ROUTE
LRC.OrderSevenN.fitsInterval:ROUTE    LRC.OrderSevenN.AheadArc:ROUTE
LRC.OrderSixN.MeetsBox:ROUTE          LRC.OrderSixN.IsMinimalStep:ROUTE
LRC.OrderSixN.OnOrbit:ROUTE           LRC.OrderSixN.OrbitMeets:ROUTE
LRC.OrderSixN.MinimalOnOrbit:ROUTE    LRC.OrderSixN.Lonely6:ROUTE
LRC.OrderSixN.FreeFlank:ROUTE         LRC.OrderFiveN.Parallel:ROUTE
LRC.Stepping.NoRelation:ROUTE
LRC.OrderSixN.OneOf:ROUTE             LRC.OrderSixN.S7.IsBHKLift:ROUTE
LRC.OrderSevenN.InsideCone:ROUTE
LRC.OrderEightN.FreeFlank8:ROUTE      LRC.OrderEightN.ShiftedApplies8:ROUTE
LRC.OrderEightN.RationalOpening8:ROUTE LRC.OrderEightN.ClassClear8:ROUTE
LRC.OrderEightN.ResolutionClears8:ROUTE
LRC.OrderEightN.FastPair8:ROUTE
LRC.OrderEightN.BlockSplit8:ROUTE
LRC.OrderSixN.S7.Named.Found:ROUTE    LRC.OrderSixN.S7.Named.Found6:ROUTE
"
PROPS=$(python3 - $SRC/*.lean <<'PYEOF'
import re, sys
for path in sys.argv[1:]:
    src = re.sub(r'/-.*?-/', '', open(path).read(), flags=re.S)
    ns = []
    for line in src.split('\n'):
        line = re.sub(r'--.*$', '', line)
        m = re.match(r'\s*namespace\s+([A-Za-z_][\w.\x27]*)', line)
        if m: ns.append(m.group(1)); continue
        m = re.match(r'\s*end\s+([A-Za-z_][\w.\x27]*)\s*$', line)
        if m:
            if ns and ns[-1] == m.group(1): ns.pop()
            continue
        m = re.match(r'\s*(?:noncomputable\s+)?def\s+([A-Za-z_][\w.\x27]*)\b(.*)', line)
        if m and re.search(r':\s*Prop\b', m.group(2)):
            print('.'.join(ns + [m.group(1)]))
PYEOF
)
NPROP=$(echo "$PROPS" | grep -c . )
UNREG=""
for pr in $PROPS; do
  echo "$REGISTER" | tr -s ' \n' '\n\n' | grep -q "^${pr}:" || UNREG="$UNREG $pr"
done
if [ -n "$UNREG" ]; then
  echo "  UNREGISTERED Prop-valued def(s):$UNREG"
  echo "  A Prop asserted and concluded by no theorem is invisible to build, sorry and axiom"
  echo "  checks.  Decide its standing (TARGET / ROUTE / OWED / REFUTED) and add it above."
  REG_OK=0
else
  echo "  clean ($NPROP Prop-valued defs, all registered)"
  OWEDL=$(echo "$REGISTER" | tr -s ' \n' '\n\n' | grep ':OWED$' | sed 's/:OWED//' | tr '\n' ' ')
  REFL=$(echo "$REGISTER" | tr -s ' \n' '\n\n' | grep ':REFUTED$' | sed 's/:REFUTED//' | tr '\n' ' ')
  echo "  OWED:    $OWEDL"
  echo "  REFUTED: $REFL"
  REG_OK=1
fi

step "[5] tree stability"
TREE_AT_END=$(cd "$SRC" && shasum -a 256 *.lean | sort -k2 | shasum -a 256 | cut -d' ' -f1)
if [ "$TREE_AT_START" != "$TREE_AT_END" ]; then
  echo "  tree CHANGED during this run: ${TREE_AT_START:0:12} -> ${TREE_AT_END:0:12}"
  echo "  The figures above mix two states and describe a tree that never existed.  Re-run."
  STABLE_OK=0
else
  echo "  clean (digest ${TREE_AT_END:0:12})"
  STABLE_OK=1
fi

echo "== total: $((SECONDS-T0))s =="
echo
if [ "$AX_OK" = "1" ] && [ "$COV_OK" = "1" ] && [ -z "$SORRY" ] && [ "$HYG_OK" = "1" ] \
   && [ "$REG_OK" = "1" ] && [ "$STABLE_OK" = "1" ]; then
  echo "GATE PASS (Spec layer): $NDECL declarations, axiom-clean, coverage $NDECL of $NDISK."
  echo "           This gates the SPEC LAYER only.  It does not gate the paper"
  echo "           (scripts/n8/gate.sh) or the cascade artefact (scripts/cascade/gate.sh)."
  echo "           LRC is NOT proved at any order.  The OWED items above are not theorems."
  exit 0
fi
echo "GATE FAIL."
exit 1
