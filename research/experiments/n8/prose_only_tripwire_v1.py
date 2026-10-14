"""Tripwire for the hole the cascade gate cannot see.

The gate reads "coverage N of N on disk": coverage of the LEAN TREE, not of the
manuscript's claims.  A result proved only in prose is invisible to the gate, to
#print axioms, and to every scan we run.  Propositions 6.10-6.11 lived in that hole.

This flags every numbered result in a manuscript that the section 7 crosswalk does NOT
tie to a Lean declaration.  Such a result is not thereby wrong -- it is UNCHECKED, and
must carry its index bound explicitly (CORRECTIONS_2026_09_17_v2 section 6).

Usage: prose_only_tripwire_v1.py <manuscript.md>
Exit 1 if any prose-only result lacks a stated bound, 0 otherwise.
"""
import re, sys

path = sys.argv[1] if len(sys.argv) > 1 else "docs/n8/MANUSCRIPT_v9_2.md"
text = open(path).read()

# every numbered result the manuscript states
RESULT = re.compile(r'\*\*(Theorem|Proposition|Corollary|Lemma)\s+([0-9]+\.[0-9]+[a-z]?)')
results = sorted({m.group(2) for m in RESULT.finditer(text)},
                 key=lambda s: [int(x) for x in re.findall(r'\d+', s)])

# Scope to the section 7 crosswalk ONLY.  Appendix B is a changelog and QUOTES old
# crosswalk wording verbatim; without this scoping the check fires on its own history.
# (Found exactly that way: v9_3's B.6 row quoting v9.2's "not formalised" produced three
# false positives.)  A check that cannot tell a live row from a historical one is
# measuring the text, not the claims.
lines = text.splitlines()
start = next((i for i, l in enumerate(lines) if re.match(r'^##+ *7\.', l)), 0)
end = next((i for i, l in enumerate(lines[start + 1:], start + 1)
            if re.match(r'^##+ *(8\.|Appendix)', l)), len(lines))
rows = [l for l in lines[start:end] if l.startswith('|') and l.count('|') >= 3]
PROSE = re.compile(r'not formalised|proved in the text|in the text,', re.I)
# a row is "covered" if it names at least one lowercase_with_underscores Lean identifier
LEAN = re.compile(r'`[A-Za-z][A-Za-z0-9_.]*_[A-Za-z0-9_.]*`')

covered, prose_rows = set(), []
for r in rows:
    nums = re.findall(r'([0-9]+\.[0-9]+[a-z]?)', r)
    if not nums:
        continue
    if PROSE.search(r):
        prose_rows.append((nums, r.strip()))
    elif LEAN.search(r):
        covered.update(nums)

# a bound counts as stated if the row or the result's own paragraph says so
BOUND = re.compile(r'bound|cap|capped|at most|≤|finite|within', re.I)

print(f"manuscript            : {path}")
print(f"numbered results      : {len(results)}")
print(f"tied to Lean by §7    : {len(covered)}")
flagged = []
for nums, row in prose_rows:
    has_bound = bool(BOUND.search(row))
    for n in nums:
        flagged.append((n, has_bound, row[:100]))
print(f"prose-only rows in §7 : {len(prose_rows)}")
print()
if not flagged:
    print("no prose-only rows found -- tripwire did not fire")
else:
    print("PROSE-ONLY (invisible to the gate):")
    for n, hb, row in flagged:
        mark = "bound stated" if hb else "NO BOUND STATED"
        print(f"  {n:6s} [{mark}]  {row}...")
bad = [f for f in flagged if not f[1]]
print()
print(f"VERDICT: {len(bad)} prose-only result(s) with no stated index bound.")
sys.exit(1 if bad else 0)

# ---------------------------------------------------------------------------
# WHAT THIS DOES AND DOES NOT DO.
#
# Validated by firing on the known case: run against MANUSCRIPT_v9_2 it flags 6.10 and
# 6.11 -- the two withdrawn on 2026-09-17 -- with no knowledge of what they contain, from
# "prose-only and no bound stated" alone.  A keyword sweep found them only because their
# grade tags self-declared "residue count" and "pigeonhole".  It also flags 6.7, section
# 6.6 and section 6.2, which were prose-only in v9_2 and turned out sound once formalised:
# the flag means UNCHECKED, never wrong.
#
# Limits, stated rather than papered over:
#  * "tied to Lean by section 7" counts section references (4.5, 6.9) alongside numbered
#    results, so that number runs ahead of the result count.  It is a coverage indicator,
#    not a bijection, and no verdict is taken from it.
#  * The bound test is a regex over the crosswalk row.  A row could say "bound" and mean
#    something else.  It is a prompt to look, not a proof that a bound exists.
#  * It reads the crosswalk table, so a result the crosswalk omits entirely is invisible
#    to this check too.  That is the next hole, and it is not closed here.
