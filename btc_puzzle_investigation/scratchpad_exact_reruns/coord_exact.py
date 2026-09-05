# EXACT rerun of coord_interference quantization: is |F[a,b]|^2 exactly k*p ? (integer-only, no float)
def curve_pts(p, A, B):
    return [(x, y) for x in range(p) for y in range(p) if (y*y - x*x*x - A*x - B) % p == 0]

def exact_quantization(p, A, B):
    pts = curve_pts(p, A, B)
    # difference-count D[u][v] = #{(P,Q): xP-xQ=u, yP-yQ=v}  (integers)
    from collections import Counter
    D = Counter()
    for (x1,y1) in pts:
        for (x2,y2) in pts:
            D[((x1-x2) % p, (y1-y2) % p)] += 1
    n_int = 0; n_at_p = 0; total = 0; kmults = Counter()
    for a in range(p):
        for b in range(p):
            if a==0 and b==0: continue
            total += 1
            # |F[a,b]|^2 = sum_{u,v} D[u,v] zeta_p^{-(a u + b v)}  in Z[zeta_p]
            h = [0]*p
            for (u,v), c in D.items():
                h[(-(a*u + b*v)) % p] += c
            # rational  <=>  h[1]==h[2]==...==h[p-1]; then value = h[0]-h[1] (exact integer)
            if all(h[k] == h[1] for k in range(2, p)):
                val = h[0] - h[1]                 # = |F|^2, exact integer
                if val % p == 0:
                    n_int += 1; kmults[val//p]+=1
                    if val == p: n_at_p += 1
    return total, n_int, n_at_p, kmults, len(pts)

def float_quantization(p, A, B):
    import numpy as np, math
    pts = curve_pts(p, A, B)
    Amat = np.zeros((p,p))
    for (x,y) in pts: Amat[x,y]+=1.0
    F = np.abs(np.fft.fft2(Amat)); s2 = (F*F)/p
    s2[0,0]=0.0; vals = s2[s2>1e-6].ravel()
    nearest = np.round(vals)
    fni = float(np.mean(np.abs(vals-nearest) < 0.02*np.maximum(nearest,1)))
    f1  = float(np.mean(np.abs(vals-1.0) < 0.02))
    return fni, f1, len(vals)

for p,(A,B),lab in [(43,(0,7),"CM y^2=x^3+7"), (43,(1,1),"non-CM y^2=x^3+x+1"), (67,(0,7),"CM y^2=x^3+7")]:
    tot, nint, natp, km, npts = exact_quantization(p,A,B)
    fni, f1, nv = float_quantization(p,A,B)
    print(f"p={p} {lab}: {npts} pts")
    print(f"  EXACT : |F|^2/p is an exact integer for {nint}/{tot} of (a,b)!=0  ({100*nint/tot:.1f}%)  |  |F|^2==p exactly for {natp}/{tot}  |  k-multiplicity {dict(sorted(km.items()))}")
    print(f"  FLOAT : frac_near_int(2%%)={fni:.3f}  frac_at_1(2%%)={f1:.3f}   (float counts nonzero vals={nv})")
    print()
