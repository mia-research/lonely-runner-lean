import re, os, glob, importlib.util
spec = importlib.util.spec_from_file_location("cnf", "check_no_float.py"); cnf = importlib.util.module_from_spec(spec); spec.loader.exec_module(cnf)
DEC = re.compile(r"allclose|isclose|is_square|< *1e-|<= *1e-|\babs\([^)]*\) *< ")
BENIGN = re.compile(r"float\(['\"]nan|== *0[: )]|!= *0\b|den *== *0|rms *== *0|return 0\.0|float\('nan'\)|# *noqa: float")
SAGE_EXACT = re.compile(r"K\.hom|\.is_square\(\)|number_field|CyclotomicField|QQbar|\bNF\b")
STATV = re.compile(r"\bpv?\b|z\[|_z\b|zscore|p_?val|verdict *=|tie_rate|perm")
seen=set(); genuine=[]
for p in sorted(glob.glob("*.py")):
    if p.endswith((".sage.py",)) : sagey=True
    else: sagey=False
    try:
        src=open(p).read().splitlines(); vs=cnf.violations(p)
    except Exception: continue
    for ln,op in vs:
        L = src[ln-1] if ln-1<len(src) else ""
        if not DEC.search(L): continue
        if BENIGN.search(L) or SAGE_EXACT.search(L) or STATV.search(L): continue
        key=(p,L.strip())
        if key in seen: continue
        seen.add(key); genuine.append((p,ln,L.strip()[:100]))
print(f"GENUINE float-exactness-decision lines (deduped, benign/Sage/stat excluded): {len(genuine)}\n")
for f,ln,t in genuine: print(f"  {f}:{ln}: {t}")
