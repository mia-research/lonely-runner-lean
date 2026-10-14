"""Section 5 nativeness pass for the 22 declarations added in v9.3.

Section 5's claim is a SOURCE-LEVEL claim about the identifiers a declaration uses:
"Every non-local identifier they use is Int.fract and its four lemmas, Nat.cast, ...
Nothing from measure theory, topology, filters or number theory appears in them, and no
statement of equidistribution, Weyl, Kronecker or Dirichlet type is used in any of them."

This extracts every dotted identifier from the source of each new declaration and sorts it
into local (this artefact), allowed-foundational, or FLAGGED.  It reads what is WRITTEN,
which is the same reading section 5 used; tactics such as nlinarith and field_simp pull
mathlib lemmas in behind the scenes and are not visible to this or to section 5's own pass.
That limit is stated, not papered over.
"""
import re, subprocess, sys, pathlib

CASCADE = pathlib.Path("LonelyRunner/LonelyRunner/LRC/Cascade")
new = [l.strip() for l in open("/tmp/newdecls.txt") if l.strip()]

# local names: anything declared anywhere in the cascade artefact
local = set()
for f in CASCADE.glob("*.lean"):
    for m in re.finditer(r'^(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev|structure)\s+([A-Za-z_][A-Za-z0-9_\']*)',
                         f.read_text(), re.M):
        local.add(m.group(1))

# the foundational set section 5 permits, plus ordinary core/order/ring algebra
ALLOWED_PREFIX = ("Int.", "Nat.", "List.", "Finset.", "Function.", "Rat.", "Real.")
ALLOWED_EXACT = {"Fact.out", "Classical.choice", "Quot.sound", "Ne.symm", "Or.inl", "Or.inr",
                 "Subtype.val", "Set.range", "Dvd.dvd"}
# the categories section 5 says must NOT appear
BANNED_RE = re.compile(r'\b(MeasureTheory|Topology|Filter|Nat\.Prime|NumberTheory|'
                       r'Irrational|Equidistrib|Weyl|Kronecker|Dirichlet|Polynomial|'
                       r'Matrix|Complex|Analysis)\b')

def body_of(name):
    for f in CASCADE.glob("*.lean"):
        t = f.read_text()
        m = re.search(r'^(?:noncomputable\s+)?(?:theorem|lemma|def)\s+' + re.escape(name) + r'\b', t, re.M)
        if not m:
            continue
        rest = t[m.start():]
        nxt = re.search(r'\n(?:/--|@\[|(?:noncomputable\s+)?(?:theorem|lemma|def|end)\s)', rest[10:])
        return f.name, rest[:nxt.start() + 10] if nxt else rest
    return None, ""

flagged, used_nonlocal = {}, {}
for name in new:
    fn, body = body_of(name)
    if not body:
        print(f"  ?? could not locate {name}")
        continue
    ids = set(re.findall(r'\b([A-Z][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_\']*)+)\b', body))
    ids |= set(re.findall(r'\b([a-z][A-Za-z0-9_]*\.[A-Za-z_][A-Za-z0-9_\']*)\b', body))
    # BARE capitalised identifiers too.  The first version of this script missed
    # `Irrational` because it matched only DOTTED names -- a proxy for "imported
    # identifier" rather than the thing itself.  Recorded because it is the same
    # failure this project keeps making, caught here by the check's own target.
    ids |= set(re.findall(r'\b([A-Z][A-Za-z0-9_]*)\b', body))
    nl = {i for i in ids if i.split('.')[0] not in local and i not in local}
    used_nonlocal[name] = nl
    bad = {i for i in nl if BANNED_RE.search(i)}
    if bad:
        flagged[name] = (fn, sorted(bad))

allnl = sorted(set().union(*used_nonlocal.values())) if used_nonlocal else []
print(f"declarations checked            : {len(used_nonlocal)}")
print(f"distinct non-local identifiers  : {len(allnl)}")
print()
print("FLAGGED against section 5's stated exclusions:")
if not flagged:
    print("  none")
for nm, (fn, bad) in sorted(flagged.items()):
    print(f"  {nm}  ({fn})  ->  {', '.join(bad)}")
print()
print("All non-local identifiers used, for the record:")
for i in allnl:
    print(f"  {i}")
