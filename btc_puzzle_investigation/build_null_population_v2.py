#!/usr/bin/env python3
"""Regenerate the NULL_RETEST population. Committed so the denominator is auditable.
Gate defect #8: v1 was built by a scratchpad script that no longer existed."""
import os, re, glob, json, hashlib

NULLWORD = re.compile(r"\b(null|refut|no signal|no leak|no lever|vacuous|dissolv|retract|void|"
                      r"generic|bounded to nothing|no residual|no structure|artifact|artefact|"
                      r"not a leakage|0 operational|fails|failed|no effect|flat|inadmissible|"
                      r"moot|superseded|withdrawn)\b", re.I)
GRADE  = re.compile(r"\[(?:PROVED|VERIFIED|EMPIRICAL|CITED|ASSERTED|HEURISTIC|null|NULL|OPEN|GAP|CLOSED|PROVISIONAL)[^\]]*\]")
SCRIPT = re.compile(r"[A-Za-z0-9_./-]+\.(?:py|sage)")
BANNER = re.compile(r"WITHDRAWN|SUPERSEDED|\bVOID\b|RETRACT|DO NOT RUN", re.I)
SPEC_PREFIX = ("PREREG","PLAN","PROTOCOL","KNOWN_FACTS","POSITIVE_FINDINGS_MASTER","VOID",
               "OPEN_","VERIFY_SPEC","btc_puzzle_research_plan")
GUARDS = {"check_no_float.py","check_ledger.py","ecc_secp256k1.py","smoke_test.py"}

# --- output typing (gate §2). First pass, mechanical; each row confirmed before its arms launch.
def classify(txt, claim=""):
    """Type on the CLAIM first (the statistic being asserted); fall back to the document.
    Typing on whole-document text lets any stray p-value anywhere outrank the real statistic."""
    for t in (claim.lower(), txt.lower()):
        if not t.strip(): continue
        r = _classify_one(t)
        if r != "T7": return r
    return "T7"

def _classify_one(t):
    if re.search(r"\bp\s*=\s*0?\.\d|\bp-value|\bpermutation|\bresampl", t):        return "T3"
    if re.search(r"\bpercentile|\bpct\b|\brank\b.*\bnull\b", t):                    return "T4"
    if re.search(r"\bz\s*=\s*[-+]?\d|\bstouffer|\bsigma\b|\bz-score", t):           return "T5"
    if re.search(r"≤\s*2[⁻^]|\bbound(ed|s)?\b|\bwithin\s+√|\bO\(|\bat most\b", t):    return "T6"
    if re.search(r"\bexact\b|\binteger\b|\d+/\d+\b|\bvanish|\bdivisib|\bdimension", t): return "T1"
    if re.search(r"\bholds\b|\btrue\b|\bfalse\b|\biff\b|\b⟺", t):                   return "T2"
    return "T7"                                     # prose-only: not admissible, must be reformulated

rows = []
for f in sorted(glob.glob("*.md")):
    txt = open(f, encoding="utf-8", errors="replace").read()
    if not NULLWORD.search("\n".join(txt.splitlines()[:6])): continue
    claim = ""
    for ln in txt.splitlines():
        s = ln.strip()
        if len(s) < 25 or s.startswith("|---"): continue
        if NULLWORD.search(s) and GRADE.search(s): claim = s; break
    if not claim:
        for ln in txt.splitlines():
            s = ln.strip()
            if len(s) > 25 and NULLWORD.search(s): claim = s; break
    scripts = [s for s in dict.fromkeys(SCRIPT.findall(txt)) if not s.endswith(".md")]
    present = [s for s in scripts if os.path.exists(os.path.basename(s))]
    first   = (present or scripts or [""])[0].split("/")[-1]
    claim   = re.sub(r"\s+", " ", claim)[:200]

    if f.startswith(SPEC_PREFIX):      typ, status = "T8", "NOT-A-NULL"
    elif BANNER.search(claim):         typ, status = "T8", "NOT-A-NULL"
    elif first in GUARDS or not present: typ, status = classify(txt, claim), "NO-REPRO"
    else:
        typ = classify(txt, claim)
        status = "REFORMULATE" if typ == "T7" else "PENDING"
    sha = ""
    if present and os.path.exists(os.path.basename(present[0])):
        sha = hashlib.sha256(open(os.path.basename(present[0]),"rb").read()).hexdigest()[:12]
    rows.append(dict(doc=f, claim=claim, scripts=scripts[:3], present=present[:3],
                     script=first, sha=sha, type=typ, status=status,
                     repro=bool(present) and first not in GUARDS))

core = [r for r in rows if r["status"] == "PENDING"]
core.sort(key=lambda r: r["doc"])
for i, r in enumerate(core): r["batch"] = i // 14 + 1
for r in rows:
    if r["status"] != "PENDING": r["batch"] = 0

json.dump(rows, open("null_population_v2.json","w"), indent=1)
from collections import Counter
print(f"population            {len(rows)}")
print(f"  NOT-A-NULL          {sum(1 for r in rows if r['status']=='NOT-A-NULL')}  (spec/plan docs + withdrawn banners)")
print(f"  NO-REPRO            {sum(1 for r in rows if r['status']=='NO-REPRO')}")
print(f"  REFORMULATE (T7)    {sum(1 for r in rows if r['status']=='REFORMULATE')}")
print(f"  PENDING  = n_core   {len(core)}   batches {max(r['batch'] for r in core)}")
print("  types in n_core:", dict(sorted(Counter(r['type'] for r in core).items())))
