from fractions import Fraction as F

def bad_intervals(s):
    """open intervals where ||s t|| < 1/8"""
    out=[]
    for k in range(0,s+1):
        lo,hi=max(F(8*k-1,8*s),F(0)),min(F(8*k+1,8*s),F(1))
        if lo<hi: out.append((lo,hi))
    return out

def good(S):
    iv=[]
    for s in S: iv+=bad_intervals(s)
    iv.sort(); m=[]
    for lo,hi in iv:
        if m and lo<m[-1][1]: m[-1][1]=max(m[-1][1],hi)     # STRICT
        else: m.append([lo,hi])
    g=[]; cur=F(0)
    for lo,hi in m:
        if cur<=lo: g.append((cur,lo))
        cur=max(cur,hi)
    if cur<=1: g.append((cur,F(1)))
    return [(a,b) for a,b in g if a<=b and not(a==b==0) and not(a==b==1)]

def measure(G): return sum(b-a for a,b in G)
def widest(G): return max((b-a for a,b in G), default=F(0))

cases=[('AP r1/r7', [1,2,3,4,5,6]),
       ('AP r2/r6', [1,2,3,4,5]),
       ('AP r3/r5', [1,2,3,4]),
       ('AP r4   ', [1,2,3]),
       ('E* r1   ', [2,6,7,8,10,13]),
       ('E* r7   ', [3,5,6,7,11,13]),
       ('E* r4   ', [1,3,5,6,7])]

for nm,Fx in cases:
    GF=good(Fx); mF=measure(GF); target=F(3,4)*mF
    print(f'{nm}  F={Fx}')
    print(f'     |G_F| = {mF} = {float(mF):.6f}     3/4*|G_F| = {float(target):.6f}')
    vals=[]
    for e in range(1,241):
        if e in Fx: continue
        Ge=good(sorted(set(Fx+[e]))); m=measure(Ge)
        vals.append((e,m,widest(Ge)))
    mn=min(vals,key=lambda t:t[1])
    zero=[v for v in vals if v[1]==0]
    tail=[v[1] for v in vals if v[0]>160]
    print(f'     min over e<=240: |G| = {mn[1]} = {float(mn[1]):.6f} at e={mn[0]}   widest component there = {float(mn[2]):.6f}')
    print(f'     e with |G| = 0: {len(zero)}' + (f'  -> {[z[0] for z in zero[:8]]}' if zero else '   (none)'))
    print(f'     tail mean |G| (e in 161..240) = {float(sum(tail)/len(tail)):.6f}   ratio to 3/4*|G_F| = {float(sum(tail)/len(tail)/target):.4f}')
    print()
