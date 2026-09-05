#!/usr/bin/env python3
"""v3 — follow each null claim to its ARTIFACT and ask whether the artifact carries
power and scope that the claim line drops.

v2 audited the claim line alone, so it could only say 'this row needs checking'.
CLAIMS.md rule 3: the ledger indexes STATUS; the full statement lives in the named artifact.
So a row is only an overclaim if the ARTIFACT also fails to carry it."""
import re, json, glob, os

POWER = re.compile(r"\bMDE\b|\bpower\b|\bfloor\b|detectab\w+|\bFPR\b|α\s*=|\balpha\s*=|\bSE\b|"
                   r"\b95%\s*CI\b|\bCI\b|\bp[_ ]?perm\b|\bp\s*=\s*0?\.\d|\bB\s*=\s*\d|"
                   r"\bN\s*=\s*\d|\bsensitivit\w+|\bresolv\w+", re.I)
SCOPE = re.compile(r"\bp\s*[≤<]\s*2\^|\bp\s*∈\s*\[|\bband\b|model scale|at this power|"
                   r"\b\d+\s*primes?\b|at matched|\bp\s*≤\s*\d|\bp\s*∈|\brange\b|\bN\s*=\s*\d", re.I)

rows = json.load(open("null_scoping_audit_v2.json"))
corpus = {f: open(f, encoding="utf-8", errors="replace").read() for f in glob.glob("*.md")}

def find_artifact(text, src):
    """the artifact a claim names: a backticked *.md / *.py in the claim, else the source doc."""
    for m in re.findall(r"`([A-Za-z0-9_./-]+\.(?:md|py|sage))`", text):
        b = os.path.basename(m)
        if b in corpus: return b
        if os.path.exists(b): return b
    return None if src.startswith("CLAIMS.md") else src

settled = []
for r in rows:
    if r["verdict"] in ("SCOPED", "ANALYTICAL"): continue
    art = find_artifact(r["text"], r["src"])
    if art and art in corpus:
        body = corpus[art]
        ap, asc = bool(POWER.search(body)), bool(SCOPE.search(body))
        v = "ARTIFACT-CARRIES" if (ap and asc) else ("ARTIFACT-PARTIAL" if (ap or asc) else "ARTIFACT-BARE")
    elif art and art.endswith((".py", ".sage")):
        v = "SCRIPT-ONLY"
    else:
        v = "NO-POINTER"   # the LEDGER ROW names no artifact. NOT a claim that none
                           # exists — M25/N15 both have artifacts. This is a CLAIMS.md
                           # rule 3 violation: "Never compress a row by deleting its
                           # artifact pointer — that is precisely the v12->v14 loss."
    settled.append(dict(src=r["src"], claim_verdict=r["verdict"], artifact=art or "—",
                        artifact_verdict=v, text=r["text"][:105]))

from collections import Counter
c = Counter(s["artifact_verdict"] for s in settled)
print(f"rows flagged by v2 (PARTIAL/UNDERSCOPED): {len(settled)}\n")
for k in ("ARTIFACT-CARRIES","ARTIFACT-PARTIAL","ARTIFACT-BARE","SCRIPT-ONLY","NO-POINTER"):
    print(f"  {k:18s} {c[k]:3d}")
print(f"\n  => {c['ARTIFACT-CARRIES']} rows are ledger-compression only: the artifact carries "
      f"power+scope, the ledger line dropped it.")
print(f"  => {c['ARTIFACT-BARE']} rows have no scope in claim OR artifact.")
json.dump(settled, open("null_scoping_audit_v3.json","w"), indent=1)
print("\n--- ledger rows carrying no artifact pointer (rule 3) ---")
for s in settled:
    if s["artifact_verdict"] in ("ARTIFACT-BARE","NO-POINTER"):
        print(f"  {s['src']:<52} [{s['artifact_verdict']}]  {s['text'][:78]}")
