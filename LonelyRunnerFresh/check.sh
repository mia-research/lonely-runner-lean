#!/bin/bash
# check.sh for LonelyRunnerFresh (2026-10-07, v2).  Usage: ./check.sh [Fresh/File.lean ...]  (default: all, in import order)
# Type-checks with plain `lean` against the EXISTING repo's mathlib build, read-only: LEAN_PATH comes from
# `lake env printenv LEAN_PATH` in the repo with the repo's own LonelyRunner build directory REMOVED, so nothing under
# LonelyRunner/ can be imported or written.  Fresh modules are compiled in import order to build/ (inside this folder)
# so later modules can `import Fresh.X`.  No `lake build` is run anywhere.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/.." && pwd)"
LP="$(cd "$REPO" && lake env printenv LEAN_PATH)"
LP="$(echo "$LP" | tr ':' '\n' | grep -v "^$REPO/.lake/build/lib/lean$" | paste -sd: -)"
export LEAN_PATH="$HERE/build:$LP"
cd "$HERE"
mkdir -p build/Fresh
ORDER=$(python3 - "$@" <<'PY'
import re,sys,glob,os
files=sorted(glob.glob("Fresh/*.lean"))
deps={}
for f in files:
    m=os.path.basename(f)[:-5]
    deps[m]=[x for x in re.findall(r"^import Fresh\.(\w+)",open(f).read(),re.M)]
seen=[];tmp=set()
def visit(m):
    if m in seen: return
    if m in tmp: print("CYCLE",m,file=sys.stderr); sys.exit(2)
    tmp.add(m)
    for d in deps.get(m,[]): visit(d)
    tmp.discard(m); seen.append(m)
for m in deps: visit(m)
want=set(os.path.basename(a)[:-5] for a in sys.argv[1:])
for m in seen:
    if not want or m in want: print("Fresh/%s.lean"%m)
PY
)
fail=0
for f in $ORDER; do
  m=$(basename "$f" .lean)
  echo "== lean $f"
  if ! lean "$f" -R . -o "build/Fresh/$m.olean" 2>&1; then fail=1; fi
done
echo "== scan for sorry / native_decide / axiom / admit / unsafe (code lines, comments stripped)"
for f in $ORDER; do
  python3 - "$f" <<'PY'
import re,sys
s=open(sys.argv[1]).read()
s=re.sub(r"/-.*?-/","",s,flags=re.S)
s=re.sub(r"--[^\n]*","",s)
for w in ("sorry","native_decide","axiom","admit","unsafe"):
    n=len(re.findall(r"\b"+w+r"\b",s))
    print("  %-26s %-14s %d"%(sys.argv[1],w,n))
PY
done
echo "== Prop registry: every 'def/structure ... : Prop' needs a '-- STANDING:' tag directly above (after any docstring)"
python3 - $ORDER <<'PY'
import re,sys
bad=0
for f in sys.argv[1:]:
    L=open(f).read().split("\n")
    for i,l in enumerate(L):
        if re.match(r"\s*(noncomputable )?(def|structure|abbrev)\b.*:\s*Prop\b",l):
            j=i-1
            while j>=0 and L[j].strip()=="" : j-=1
            m=re.search(r"STANDING:\s*(\w+)",L[j]) if j>=0 else None
            tag=m.group(1) if m else None
            name=re.search(r"(def|structure|abbrev)\s+(\S+)",l).group(2)
            print("  %-34s %-10s %s:%d"%(name,tag,f,i+1))
            if tag is None: bad+=1
print("  untagged:",bad)
PY
exit $fail
