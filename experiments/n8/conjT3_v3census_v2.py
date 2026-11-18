# conjT3_v3census_v1 -- the V3 frontier census (rho6 > 17, rho7 >= 25).
# Structural: readings > 9 have their k=1 zone below 1, so rho6, rho7 contribute NO
# zones in [1,7].  K6 = [1,7] \ zones(rho2..rho5).  Carve needs every component in a
# single rho7-zone (Lemma E).  Whole-column test over rho7 in [25,130).
import itertools, sys
from fractions import Fraction as F
from taillemma_lib_v1 import zones_of

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

def column_state(rho_small, rlo, rhi):
    comps = k6_components(rho_small)
    if not comps: return False, {'kind':'K6-EMPTY','idx':None}
    cur = None
    for i,(a,b) in enumerate(comps):
        fs = feasible_set(a,b,rlo,rhi)
        new = fs if cur is None else intersect(cur,fs)
        if not new:
            kind = 'COMP-DEAD' if not fs else 'INTERSECT-DIE'
            return True, {'kind':kind,'idx':i,'comp':(str(a),str(b)),'ncomp':len(comps)}
        cur = new
    return False, None

# grid: rho2..rho5 exact values over the zone-contributing range (1,17], plus
# zone-free sentinels 18/25 (for rho5.. only; monotone)
GRID_DENSE = [F(12,10),F(2),F(5,2),F(3),F(7,2),F(4),F(9,2),F(5),F(11,2),F(6),F(13,2),F(7),
              F(15,2),F(8),F(17,2),F(9),F(19,2),F(10),F(21,2),F(11),F(23,2),F(12),F(25,2),F(13),
              F(27,2),F(14),F(29,2),F(15),F(31,2),F(16),F(33,2),F(17),F(18),F(20),F(25),F(30),F(40)]
RLO, RHI = F(25), F(130)
alive = []; kills = {'COMP-DEAD':0,'INTERSECT-DIE':0,'K6-EMPTY':0}; total = 0
survivor_comps = []
for rho in itertools.combinations_with_replacement(GRID_DENSE, 4):
    total += 1
    dead, info = column_state(list(rho), RLO, RHI)
    if dead:
        kills[info['kind']] += 1
        if info['kind'] != 'K6-EMPTY' and kills[info['kind']] <= 3:
            pass
    else:
        alive.append(rho)
        if len(alive) <= 10: survivor_comps.append((rho, k6_components(list(rho))))
print("V3 census: tuples=%d | kills=%s | ALIVE=%d" % (total, kills, len(alive)))
for rho, comps in survivor_comps:
    print("  ALIVE rho2..5:", [str(x) for x in rho], "| comps:", [(str(a)[:8],str(b)[:8]) for a,b in comps])
