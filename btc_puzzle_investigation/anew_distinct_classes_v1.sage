# Completes the pre-committed reporting requirement PREREG v2 sec.4 [G:M-6]:
# report DISTINCT cover-isomorphism classes, not raw (p,f) rows.
# Same canonical labelling as anew_cartier_audit_v2.sage : cover_class().
import random
load("anew_cartier_audit_v2.sage") if False else None
SEED = 20260803; N_RANDOM = 6
CURATED = [("x^3+7",[7,0,0,1]),("x^3+2",[2,0,0,1]),("x^3+11",[11,0,0,1]),
           ("x^3+2x+5",[5,2,0,1]),("x^3+x+1",[1,1,0,1]),("x^3-x+3",[3,-1,0,1])]
MAIN    = [p for p in prime_range(212, 500) if p % 4 == 3 and p != 251] + [1031, 1039]
CONTROL = [p for p in prime_range(198, 500) if p % 4 == 1 and p != 257] + [1021, 1033]

def cover_class(p, fco):
    Fp = GF(p); R = PolynomialRing(Fp,'x'); x = R.gen()
    f = R([Fp(c) for c in fco]); a3 = f[3]; f = f/a3; f = f(x - f[2]/3)
    P, Q = f[1], f[0]
    g = gcd(4, p-1); z = Fp.multiplicative_generator()**((p-1)//g)
    def coset(u):
        v = u**((p-1)//g)
        for e in range(g):
            if z**e == v: return e
    best = None
    for al in Fp:
        if al == 0: continue
        cand = (ZZ(P/al**2), ZZ(Q/al**3), coset(a3*al**3))
        if best is None or cand < best: best = cand
    return best

for tag, plist, sd in (("MAIN", MAIN, int(SEED)), ("CONTROL", CONTROL, int(SEED+1))):
    rng = random.Random(sd)
    rows = 0; classes = 0
    for p in plist:
        Fp = GF(p); R = PolynomialRing(Fp,'x')
        fs = [co for _, co in CURATED]
        drawn = 0
        while drawn < N_RANDOM:
            co = [rng.randrange(p) for _ in range(3)] + [rng.randrange(1,p)]
            if R([Fp(c) for c in co]).discriminant() != 0:
                fs.append(co); drawn += 1
        lab = set()
        for co in fs:
            if R([Fp(c) for c in co]).discriminant() == 0: continue
            rows += 1; lab.add(cover_class(p, co))
        classes += len(lab)
    print("%-8s rows = %-5d distinct cover-isomorphism classes = %-5d  (collapse %d)"
          % (tag, rows, classes, rows - classes))
