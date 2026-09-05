#!/usr/bin/env python3
"""Classify every float-flagged line into SAFE (auto-annotatable) vs REVIEW (must fix).
Dry-run report by default; --apply writes justified noqa to the SAFE buckets only."""
import re, sys, os, glob, importlib.util
spec = importlib.util.spec_from_file_location("cnf", os.path.join(os.path.dirname(os.path.abspath(__file__)), "check_no_float.py"))
cnf = importlib.util.module_from_spec(spec); spec.loader.exec_module(cnf)

DECISION = re.compile(r"allclose|isclose|is_square|< *1e-|<= *1e-|== *0\b|!= *0\b|\babs\([^)]*\) *< ")
DECVAR   = re.compile(r"\b(ok|pass|hold|verdict|null|vanish|square|rigid|detect|match|equal|eqok|is_[a-z]+|holds|passed|_ok)\b *=")
SMEARVAR = re.compile(r"\b(d|dd|key|priv|privkey|scalar|target|secret|D|Xi|Yi|x_?P|y_?P|raw)\b")
MODCTX   = re.compile(r"% *[pPnN]\b|pow\([^)]*,[^)]*,[^)]*\)|limit_denominator|Fraction")
DISPLAY  = re.compile(r"print\(|f['\"].*\{|\.format\(|logging\.|log\.(info|debug)|stdout|f-?string|:\.[0-9]+[fdge]")
STAT     = re.compile(r"np\.(mean|std|var|average|median|percentile|corrcoef|cov)|corrcoef|z *=|zscore|entropy|mutual_info|\.corr\(|permutation")
SKLEARN  = re.compile(r"astype\(float\)")

def classify(fileexts, line):
    L = line
    if DISPLAY.search(L):                                   return "SAFE-DISPLAY", "display/log only"
    if DECISION.search(L) or DECVAR.search(L):              return "REVIEW-DECISION", None
    if re.search(r"float\(|astype\(float\)|np\.log2?\(|\*\*0\.5", L) and SMEARVAR.search(L) and not MODCTX.search(L):
        return "REVIEW-SMEAR", None
    if STAT.search(L):                                      return "SAFE-STAT", "matched-null statistic on exact data"
    if SKLEARN.search(L) and fileexts["sklearn"]:          return "SAFE-SKLEARN", "sklearn input; features are small residues (<2^53)"
    return "REVIEW-OTHER", None

buckets = {}
review = {"REVIEW-DECISION": [], "REVIEW-SMEAR": [], "REVIEW-OTHER": []}
here = os.path.dirname(os.path.abspath(__file__))
files = sorted(glob.glob(os.path.join(here, "*.py")))
for p in files:
    try:
        src = open(p).read().splitlines()
        vs = cnf.violations(p)
    except Exception:
        continue
    ctx = {"sklearn": bool(re.search(r"sklearn|train_test_split|LogisticRegression|RandomForest|\.fit\(|\.predict\(", "\n".join(src)))}
    for ln, op in vs:
        if "bare '# noqa" in op:  # already half-noted, needs a reason -> review
            review["REVIEW-OTHER"].append((os.path.basename(p), ln, "bare noqa")); buckets["REVIEW-OTHER"]=buckets.get("REVIEW-OTHER",0)+1; continue
        L = src[ln-1] if ln-1 < len(src) else ""
        cat, reason = classify(ctx, L)
        buckets[cat] = buckets.get(cat,0)+1
        if cat.startswith("REVIEW"):
            review[cat].append((os.path.basename(p), ln, L.strip()[:90]))

print("=== BUCKET COUNTS (flagged lines) ===")
for k in ["SAFE-DISPLAY","SAFE-STAT","SAFE-SKLEARN","REVIEW-DECISION","REVIEW-SMEAR","REVIEW-OTHER"]:
    print(f"  {k:16} {buckets.get(k,0)}")
print(f"\n=== REVIEW-DECISION (float decides a verdict — MUST exactify) : {len(review['REVIEW-DECISION'])} ===")
for f,ln,t in review["REVIEW-DECISION"][:40]: print(f"  {f}:{ln}: {t}")
print(f"\n=== REVIEW-SMEAR (float on a possible large int — MUST check) : {len(review['REVIEW-SMEAR'])} ===")
for f,ln,t in review["REVIEW-SMEAR"][:40]: print(f"  {f}:{ln}: {t}")
print(f"\n(REVIEW-OTHER: {len(review['REVIEW-OTHER'])} lines need a human/exact call)")
