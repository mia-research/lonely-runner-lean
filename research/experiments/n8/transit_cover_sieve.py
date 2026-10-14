from math import gcd
def lcm(a,b): return a*b//gcd(a,b)
def band_ok(x,m):
    r=x%m; return 8*min(r,m-r)>=m

def good_e(F,m):
    """residues e mod m for which SOME a compatible with F also clears e"""
    A=[a for a in range(m) if all(band_ok(f*a,m) for f in F)]
    if not A: return None
    return {e for e in range(m) if any(band_ok(e*a,m) for a in A)}

def sieve_e(F,Mmax=140,cap=20_000_000,verbose=False):
    L=1; surv=[0]; used=[]
    cands=[]
    for m in range(2,Mmax+1):
        G=good_e(F,m)
        if G is None or len(G)==m: 
            if G is not None and len(G)==m: return ('ALL',m,[])   # this modulus alone covers every e
            continue
        cands.append((len(G)/m,m,G))
    cands.sort(key=lambda t:-t[0])            # densest first
    for dens,m,G in cands:
        nL=lcm(L,m)
        if len(surv)*(nL//L)>cap: continue
        new=[r+k*L for r in surv for k in range(nL//L) if (r+k*L)%m not in G]
        if len(new)<len(surv)*(nL//L):
            used.append(m); L=nL; surv=new
        if not surv: return ('COVERED',L,used)
    return ('LEFT',L,(used,surv[:5],len(surv)))

cases=[('AP r1 / r7  F={1,2,3,4,5,6}',[1,2,3,4,5,6]),
       ('AP r2 / r6  F={1,1,2,3,4,5}',[1,2,3,4,5]),
       ('AP r3 / r5  F={1,2,2,3,4}',  [1,2,3,4]),
       ('AP r4       F={1,2,3,3}',    [1,2,3]),
       ('E* r1  F={2,6,7,8,10,13}',   [2,6,7,8,10,13]),
       ('E* r7  F={13,11,7,6,5,3}',   [3,5,6,7,11,13]),
       ('E* r4  F={7,5,1,1,3,6}',     [1,3,5,6,7]),
      ]
for nm,F in cases:
    st,L,info=sieve_e(sorted(set(F)))
    if st=='ALL':
        print(f'{nm:32s} -> EVERY e has a witness at the single modulus m={L}')
    elif st=='COVERED':
        print(f'{nm:32s} -> COVERED: every e has a witness. period {L:,}, moduli {info}')
    else:
        used,ex,n=info
        print(f'{nm:32s} -> {n} residue(s) survive mod {L:,}: {ex}  (moduli {used})')
