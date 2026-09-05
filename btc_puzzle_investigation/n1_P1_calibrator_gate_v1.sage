# PREREG N1 -- cell P1 ONLY: the run-blocking calibrator gate.
# Statistic: M4 = (1/n) sum_a |V(a)|^4 = sum_t |c(t)|^2 ,  c(t) = sum_d s(d) conj(s(d+t)).
# For the chi2 readouts s(d) in {-1,0,1}: c(t) and M4 are EXACT INTEGERS (no float in path).
# Additive readouts are complex (roots of unity) -> float, LABELLED, size-only.
# This run yields NO verdict on N1. It only asks: do KNOWN-rank objects separate?
import numpy as np, sys
def PR(*a): print(*a); sys.stdout.flush()

def M4_exact_int(s, n):                      # s integer array
    c = np.array([int(np.dot(s, np.roll(s,-t))) for t in range(n)], dtype=object)
    return sum(int(x)*int(x) for x in c)      # exact python int

def M4_float(s, n):                           # complex s
    V = np.fft.fft(s); return float((np.abs(V)**4).sum()/n)

def run(p, B=7):
    E=EllipticCurve(GF(p),[0,B]); n=E.order()
    if not is_prime(n) or n<1200: return
    G=E.gens()[0]
    xs=np.zeros(n,dtype=np.int64); ys=np.zeros(n,dtype=np.int64)
    P=E(0)
    for d in range(1,n):
        P=P+G; x,y=P.xy(); xs[d]=ZZ(x); ys[d]=ZZ(y)
    c2y=np.array([0]+[kronecker(int(ys[d]),p) for d in range(1,n)],dtype=np.int64)
    c2x=np.array([0]+[kronecker(int(xs[d]),p) for d in range(1,n)],dtype=np.int64)
    rng=np.random.default_rng(int(12345))
    rnd=np.concatenate([[0],rng.choice([-1,1],size=int(n-1))]).astype(np.int64)
    ep=lambda v: np.exp(2j*np.pi*(v.astype(float))/p)
    bx   = np.concatenate([[0],ep(xs[1:])])
    bxcy = np.concatenate([[0],ep((xs[1:]+ys[1:])%p)])
    rows=[("chi2(y)  [nominal dim 4]", M4_exact_int(c2y,n)/float(n)**2, "exact int"),
          ("chi2(x)  [nominal dim 2]", M4_exact_int(c2x,n)/float(n)**2, "exact int"),
          ("random +-1 [rank ~ n]",    M4_exact_int(rnd,n)/float(n)**2, "exact int"),
          ("bx       [nominal dim 3]", M4_float(bx,n)/float(n)**2,      "float"),
          ("bx+cy    [nominal dim 4]", M4_float(bxcy,n)/float(n)**2,    "float")]
    PR("\np=%d n=%d"%(p,n))
    for name,val,tag in rows:
        PR("   %-26s  M4/n^2 = %10.4f   (%s)"%(name,val,tag))

for p in (1303, 2143, 3187):
    run(p)
PR("\nP1 GATE: known-rank objects must ORDER by rank and separate.")
PR("If dim-2 / dim-3 / dim-4 do not separate, the statistic has no rank resolution")
PR("and NOTHING it says about chi2(y) is interpretable. No N1 verdict either way.")
