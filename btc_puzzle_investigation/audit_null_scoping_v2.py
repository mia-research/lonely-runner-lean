#!/usr/bin/env python3
"""v2.1 — audit only STATED NULL CLAIMS  (v2 truncated rows to 170 chars BEFORE
testing them, so scope/power past the cutoff was invisible; fixed)

v2 — audit only STATED NULL CLAIMS, not every line containing a negative word.

v1 matched 'never/cannot/is not' anywhere and returned 629 hits, most of them rules, prose and
proof statements. That is a proxy, not the object. The object here is: a line that ASSERTS A NULL
RESULT. Scoped to (a) claim-table rows in CLAIMS.md A.2/A.3/Retracted, (b) the extracted claim line
of each core document. Reports what a claim CARRIES, never whether its numbers are right."""
import re, json

NULLCLAIM = re.compile(r"\[null[^\]]*\]|\bscoped null\b|\bnull\b.*\b(artifact|artefact)\b|"
                       r"\bno lever\b|\bno residual\b|\bno leak\b|\bno signal\b|\b0 operational\b|"
                       r"\bnot a leakage\b|\bno reduction\b|\brefuted\b|\bdissolved\b|"
                       r"\bno structure\b|\bno arithmetic content\b|\bcannot test\b|"
                       r"\bno operational\b|\bwithin noise\b|\bat[- ]floor\b|\bflat\b", re.I)
POWER  = re.compile(r"\bMDE\b|\bpower\b|\bfloor\b|detectab\w+|\bFPR\b|α\s*=|\bSE\b|\bCI\b|"
                    r"\bp[_ ]?perm\b|\bp\s*=\s*0?\.\d|\bB\s*=\s*\d|\bN\s*=\s*\d|\d+\s*/\s*\d+", re.I)
SCOPE  = re.compile(r"\bp\s*[≤<]\s*2\^|\bp\s*∈|\bband\b|model scale|\bscoped\b|at this power|"
                    r"\b\d+\s*primes?\b|at matched|\b2\^?\{?\d{1,3}\}?\b|\bp\s*≤\s*\d|"
                    r"\bconstructed\b|\breal 82\b|\bsecp\b", re.I)
ANALYT = re.compile(r"\[PROVED[^\]]*\]|\btheorem\b|\bidentity\b|for all p|scale[- ]immune|"
                    r"uniform in p|analytical closure|\bderivation\b", re.I)

rows = []
# (a) CLAIMS.md claim-table rows only
for i, ln in enumerate(open("CLAIMS.md", encoding="utf-8", errors="replace").read().splitlines(), 1):
    s = ln.strip()
    if not s.startswith("|") or s.startswith("|---") or "| # |" in s: continue
    if not NULLCLAIM.search(s): continue
    rows.append(dict(src=f"CLAIMS.md:{i}", text=re.sub(r"\s+"," ",s)))
# (b) extracted claim line of each core doc
for r in json.load(open("null_population_v2.json")):
    if r["status"] != "PENDING" or not NULLCLAIM.search(r["claim"]): continue
    rows.append(dict(src=r["doc"], text=r["claim"]))

for r in rows:
    t = r["text"]
    r["analytical"], r["power"], r["scope"] = bool(ANALYT.search(t)), bool(POWER.search(t)), bool(SCOPE.search(t))
    r["verdict"] = ("ANALYTICAL" if r["analytical"] else
                    "SCOPED" if (r["power"] and r["scope"]) else
                    "PARTIAL" if (r["power"] or r["scope"]) else "UNDERSCOPED")
from collections import Counter
c = Counter(r["verdict"] for r in rows)
print(f"STATED NULL CLAIMS audited: {len(rows)}   (v1's line-grep returned 629 — 93% of them not null claims)\n")
for k in ("ANALYTICAL","SCOPED","PARTIAL","UNDERSCOPED"): print(f"  {k:12s} {c[k]:4d}")
print(f"\n  empirical nulls carrying NEITHER power nor scope on the claim line: {c['UNDERSCOPED']}"
      f"  ({100*c['UNDERSCOPED']//max(len(rows),1)}%)")
json.dump(rows, open("null_scoping_audit_v2.json","w"), indent=1)
print("\n--- CLAIMS.md ledger rows, worst first ---")
for r in rows:
    if r["src"].startswith("CLAIMS.md") and r["verdict"] in ("UNDERSCOPED","PARTIAL"):
        print(f"  [{r['verdict']:11s}] {r['src']}  {r['text'][:120]}")
