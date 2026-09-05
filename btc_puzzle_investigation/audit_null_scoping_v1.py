#!/usr/bin/env python3
"""Does each null carry its scope, or does it overclaim?

Project rule: an EMPIRICAL null bounds the instrument, the sample and the power — it does not
close an avenue. Only an ANALYTICAL null (a proof) may speak unconditionally.
`feedback_closure_grade_2026_07_28`: to write dead/generic/vacuous/bounded-to-nothing/"must be X"
you must name OBJECT + CLASS-OF-OBSERVABLE + POWER + SCOPE, or it is an overclaim at the PROVED bar.

This reports what a statement CARRIES, never whether the number is right."""
import re, glob, json, sys

UNCOND = re.compile(r"\b(is not|are not|cannot|can't|impossible|no leak|no signal|nothing here|"
                    r"ECDLP[- ]secure|\bdead\b|ruled out|rules out|eliminat\w+|there is no|"
                    r"carries no|conveys no|no structure|no information|never\b|"
                    r"vacuous|tautolog\w+|bounded to nothing|must be computational|generic\b)", re.I)
POWER  = re.compile(r"\bMDE\b|\bpower\b|\bfloor\b|detectab\w+|sensitivit\w+|\bFPR\b|\bα\s*=|"
                    r"\balpha\s*=|\bSE\b|\bCI\b|confidence interval|\b\d{1,2}\s*%\s*power|"
                    r"\bp_?perm\b|permutation floor|\bB\s*=\s*\d|\bN\s*=\s*\d", re.I)
SCOPE  = re.compile(r"\bp\s*[≤<=]\s*2\^|\bp\s*∈|\bband\b|\bmodel scale\b|\bscoped\b|at this power|"
                    r"\bsample\b|\bN\s*=\s*\d|\b\d+\s*primes\b|\bat matched\b|"
                    r"\bwithin\b.*\brange\b|\b2\^\{?\d+|\bp\s*≤\s*\d", re.I)
ANALYT = re.compile(r"\[PROVED[^\]]*\]|\btheorem\b|\bidentity\b|\bfor all p\b|scale[- ]immune|"
                    r"uniform in p|\bproof\b|analytical closure", re.I)

def audit(path):
    txt = open(path, encoding="utf-8", errors="replace").read()
    out = []
    for i, ln in enumerate(txt.splitlines(), 1):
        s = ln.strip()
        if len(s) < 40 or s.startswith("|---") or s.startswith(">"): continue
        if not UNCOND.search(s): continue
        out.append(dict(file=path, line=i,
                        analytical=bool(ANALYT.search(s)), power=bool(POWER.search(s)),
                        scope=bool(SCOPE.search(s)), text=re.sub(r"\s+"," ",s)[:150]))
    return out

targets = ["CLAIMS.md"] + [r["doc"] for r in json.load(open("null_population_v2.json"))
                           if r["status"] == "PENDING"]
rows = [a for t in targets for a in audit(t)]

def verdict(r):
    if r["analytical"]:                      return "ANALYTICAL"       # may speak unconditionally
    if r["power"] and r["scope"]:            return "SCOPED"           # empirical, properly bounded
    if r["power"] or r["scope"]:             return "PARTIAL"          # missing one of the two
    return "UNDERSCOPED"                                               # unconditional, carries neither

for r in rows: r["verdict"] = verdict(r)
from collections import Counter
c = Counter(r["verdict"] for r in rows)
print(f"unconditional-language statements found: {len(rows)}  across {len(set(r['file'] for r in rows))} files\n")
for k in ("ANALYTICAL","SCOPED","PARTIAL","UNDERSCOPED"):
    print(f"  {k:12s} {c[k]:4d}")
print(f"\n  => UNDERSCOPED + PARTIAL = {c['PARTIAL']+c['UNDERSCOPED']} statements "
      f"({100*(c['PARTIAL']+c['UNDERSCOPED'])//max(len(rows),1)}%) speak unconditionally "
      f"without carrying both power and scope on the same line.")
json.dump(rows, open("null_scoping_audit_v1.json","w"), indent=1)

print("\n--- CLAIMS.md (the ledger everyone reads) ---")
for r in rows:
    if r["file"] == "CLAIMS.md" and r["verdict"] in ("UNDERSCOPED","PARTIAL"):
        print(f"  L{r['line']:<4} [{r['verdict']:11s}] {r['text'][:118]}")
