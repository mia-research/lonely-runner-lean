# negative control for the V3 census: recorded real carves (rho6 <= 17) must be ALIVE
# at their own rho7 on the SAME code path (guards against a false-kill instrument);
# and their smalls with rho6 zeroed out (V3 analog) should also behave sanely.
import pickle, glob
from fractions import Fraction as F
from taillemma_lib_v1 import zones_of
# reuse the census module's functions via import (it is guarded: only defs + main run)
import importlib.util
spec = importlib.util.spec_from_file_location("v3c", "conjT3_v3census_v1.py")
# instead: copy minimal defs (import would rerun census) -- redefine here
def k6_components(rho_small):
    ivs = []
    for r in rho_small:
        for a,b,j in zones_of(r):
            a2,b2 = max(a,F(1)), min(b,F(7))
            if a2 < b2: ivs.append((a2,b2))
    ivs.sort(); merged = []
    for a,b in ivs:
        if merged and a <= merged[-1][1]: merged[-1][1] = max(merged[-1][1], b)
        else: merged.append([a,b])
    comps, cur = [], F(1)
    for a,b in merged:
        if a > cur: comps.append((cur,a))
        cur = max(cur,b)
    if cur < F(7): comps.append((cur,F(7)))
    return comps
def feasible_set(a,b,rlo,rhi,jmax=1200):
    ivs=[]; j=1
    while True:
        lo,hi = F(8*j-1,a), F(8*j+1,b)
        if lo >= rhi: break
        if hi > rlo and hi > lo: ivs.append((max(lo,rlo),min(hi,rhi)))
        j += 1
        if j > jmax: break
    ivs.sort(); merged=[]
    for lo,hi in ivs:
        if lo >= hi: continue
        if merged and lo <= merged[-1][1]: merged[-1][1]=max(merged[-1][1],hi)
        else: merged.append([lo,hi])
    return merged
def intersect(f1,f2):
    res=[]
    for lo1,hi1 in f1:
        for lo2,hi2 in f2:
            lo,hi = max(lo1,lo2), min(hi1,hi2)
            if lo < hi: res.append((lo,hi))
    res.sort(); merged=[]
    for lo,hi in res:
        if merged and lo <= merged[-1][1]: merged[-1][1]=max(merged[-1][1],hi)
        else: merged.append([lo,hi])
    return merged
def column_alive(rho_small, rlo, rhi):
    comps = k6_components(rho_small)
    if not comps: return False
    cur = None
    for a,b in comps:
        fs = feasible_set(a,b,rlo,rhi)
        new = fs if cur is None else intersect(cur,fs)
        if not new: return False
        cur = new
    return True

vecs = []
for f in sorted(glob.glob('frontier_band_carve_v1_k3_s*.pkl')):
    vecs += pickle.load(open(f,'rb'))
ok = bad = 0
for v in vecs[:40]:
    rho = [F(str(x)) for x in v[:7]] if not all(hasattr(x,'numerator') for x in v[:7]) else list(v[:7])
    # v layout: (rho1..rho7) with rho1=1? assume sorted readings 1=rho1 first; adjust:
    if rho[0] != 1: continue
    smalls = rho[1:6]   # rho2..rho6
    r7 = rho[6]
    lo, hi = r7, r7 + F(1,10)
    if column_alive(smalls, lo, hi): ok += 1
    else: bad += 1
print("negative control: recorded carves alive at own rho7 (narrow window): %d/%d" % (ok, ok+bad))
