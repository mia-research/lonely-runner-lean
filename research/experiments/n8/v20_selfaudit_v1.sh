#!/usr/bin/env bash
# MECHANICAL self-audit of MANUSCRIPT_v20 against v19.
# Per CLAUDE.md 2a: a self-audit discharges the MECHANICAL layer only (statistic, exactness,
# "does the plant fire").  It does NOT discharge the FRAME layer -- object/disjointness, scope,
# falsification, pre-commitment -- which needs context isolation.  Those are named as uncovered
# at the foot of this file.
cd "$(dirname "${BASH_SOURCE[0]}")/../../docs/n8" || exit 2
A=MANUSCRIPT_v19.md; B=MANUSCRIPT_v20.md
fail=0
echo "== [1] hunk count and site attribution =="
diff -u $A $B > /tmp/v20.diff
# NOTE (fifth of this species): hunk count is a PROXY for site count.  `diff` merges sites that
# sit within its context window -- site (5), the section-8 heading, and site (4a), the 8.1 pointer,
# are adjacent and share one hunk.  Six sites therefore give SEVEN hunks, not eight.  The object is
# site attribution, which is checked by hand in the report; this number only guards against a hunk
# appearing that no site explains.
H=$(grep -c '^@@' /tmp/v20.diff); echo "  hunks: $H (expected 7; six sites, two of them adjacent and merged)"; [ "$H" = 7 ] || fail=1
echo "== [2] deletions from v19 =="
DEL=$(grep '^-' /tmp/v20.diff | grep -v '^---' | sed 's/^-//' | grep -c .)
echo "  non-blank lines removed: $DEL (expected 5, all originals of in-place rewrites)"
[ "$DEL" = 5 ] || fail=1
echo "== [3] content of the rewritten lines survives =="
# DEFECT FOUND AND FIXED 2026-09-22 (third of this species in this file).  grep -F is LINE-bounded
# and the replacements REFLOW across line breaks: "A stronger, sufficient statement is `R < 4`"
# became "A stronger,\nsufficient statement is `R < 4`,".  The content survives; the line does not.
# The object is the PHRASE, so normalise whitespace before searching.
python3 - "$B" <<'PY'
import sys, re
t=re.sub(r"\s+"," ",open(sys.argv[1]).read())
bad=0
for s in ["lonely within the nearest runner's first relative lap",
          "a plain `lake build` does not enter `LRC/`",
          "A stronger, sufficient statement is `R < 4`, lonely",
          "Two artefacts" ]:
    if s == "Two artefacts":
        print(f"  correctly absent (rewritten to Three): {s}" if s not in t else f"  UNEXPECTEDLY PRESENT: {s}")
        continue
    if s in t: print(f"  present (whitespace-normalised): {s[:64]}")
    else: print(f"  LOST: {s[:64]}"); bad=1
sys.exit(bad)
PY
[ $? -eq 0 ] || fail=1
echo "== [4] v19 header and Record of v18 byte-identical =="
# DEFECT FOUND AND FIXED 2026-09-22 (fourth of this species in this file, and the most instructive).
# The check grepped the TOKEN "Record of v18" and failed 1 vs 2 -- because the sentence in section 0
# that DESCRIBES this check contains the phrase.  The check was broken by its own documentation.
# The object is the record HEADING, a line beginning "**Record of v18**", not any mention of it.
for s in "Version 19, 2026-09-20. Supersedes v18" "Record of v18"; do
  a=$(grep -cE "^\*+${s}|^\*\*${s}\*\*|^\*${s}" $A); b=$(grep -cE "^\*+${s}|^\*\*${s}\*\*|^\*${s}" $B)
  echo "  heading '${s}': v19=$a v20=$b"; [ "$a" = "$b" ] || fail=1
done
# and the v19 header block itself must be byte-identical, which SEG A of the diff already shows;
# assert it directly rather than by token count.
python3 - "$A" "$B" <<'PY'
import sys
a=open(sys.argv[1]).read(); b=open(sys.argv[2]).read()
k="*Version 19, 2026-09-20. Supersedes v18."
blk_a=a[a.index(k):a.index("**Record of v18**")]
blk_b=b[b.index(k):b.index("\n**Record of v18**")+1]
print("  v19 header block byte-identical:", "yes" if blk_a==blk_b else "NO")
sys.exit(0 if blk_a==blk_b else 1)
PY
[ $? -eq 0 ] || fail=1
echo "== [5] grade tags: the object, not the token =="
# DEFECT FOUND AND FIXED 2026-09-22.  The first version of this check counted the TOKEN "[OPEN]"
# outside section 16 and failed on 41 -> 42.  The extra occurrence is the words "No numbered
# result, grade, `[OPEN]` item, withdrawal or figure is altered at any site" in the new section 0
# -- a MENTION of the tag name, not a tag on a claim.  The second version failed on any tag
# appearing on a removed line, which is wrong for an IN-PLACE REWRITE: the tag survives on the
# replacement.  Both are this project's recorded proxy failure (CLAUDE.md 2b).  The object is the
# CLAIM and whether it still carries its tag.
python3 - "$A" "$B" <<'PY'
import sys, subprocess
A,B=sys.argv[1],sys.argv[2]
d=subprocess.run(["diff","-u",A,B],capture_output=True,text=True).stdout
added=[l[1:] for l in d.split("\n") if l.startswith("+") and not l.startswith("+++")]
removed=[l[1:] for l in d.split("\n") if l.startswith("-") and not l.startswith("---")]
tags=["[PROVED","[VERIFIED","[EMPIRICAL]","[OPEN]","[REFUTED]","[DERIVED"]
bad=0
for rl in removed:
    for t in tags:
        if t not in rl: continue
        prefix=rl.strip()[:55]
        if any(prefix in al and t in al for al in added):
            print(f"  {t:<13} rewritten; claim and tag both survive: {prefix[:66]}")
        else:
            print(f"  {t:<13} LOST; claim no longer carries it: {prefix[:66]}"); bad=1
print("  tags introduced on genuinely new lines:")
for al in added:
    if any(rl.strip()[:55] in al for rl in removed): continue
    for t in tags:
        if t in al: print(f"    {t:<13} {al.strip()[:88]}")
sys.exit(bad)
PY
[ $? -eq 0 ] || fail=1
echo "== [6] cascade gate check [6] strings survive =="
for s in "4,759" "283 structural" "c54d9843" "c023d10" "21 modules"; do
  n=$(grep -cF "$s" $B); echo "  $s: $n"; [ "$n" -gt 0 ] || fail=1
done
echo "== [7] REFUTED items unchanged =="
for s in "DoorFirstLap" "DoorLargestFlank"; do
  a=$(grep -cF "$s" $A); b=$(grep -cF "$s" $B); echo "  $s: v19=$a v20=$b"; [ "$b" -ge "$a" ] || fail=1
done
echo "== [8] every figure section 7's new paragraph states, against the tree =="
R=../../LonelyRunner
M=$(ls $R/LonelyRunner/LRC/Spec/*.lean 2>/dev/null | wc -l | tr -d ' ')
echo "  Spec modules on disk: $M"; grep -qF "$M modules, **305 named declarations**" $B \
  && echo "  manuscript agrees" || { echo "  STALE in manuscript"; fail=1; }
G=../../experiments/nN/spec_gate_v21.out
grep -qE "GATE PASS \(Spec layer\): 305 declarations" $G \
  && echo "  gate run confirms 305" || { echo "  gate run does NOT confirm 305"; fail=1; }
echo
[ $fail = 0 ] && echo "MECHANICAL SELF-AUDIT: PASS" || echo "MECHANICAL SELF-AUDIT: FAIL"
cat <<'NOTE'

UNCOVERED BY THIS AUDIT, named explicitly (CLAUDE.md 2a: the frame layer needs isolation):
  - whether section 16's claims are DISJOINT from what sections 1-15 already assert, i.e. whether
    anything in 16 silently restates or contradicts an existing numbered result;
  - whether section 0's three "foreign shapes" are a faithful reading of v18's amendment and of
    section 6A, rather than this session's gloss on them;
  - whether any [OPEN] item of v19 is implicitly narrowed by section 16's prose without its tag moving;
  - scope of section 16's empirical figures against the populations named beside them.
Those four are what the compile-diff gate is for and a self-audit cannot substitute.
NOTE
exit $fail
