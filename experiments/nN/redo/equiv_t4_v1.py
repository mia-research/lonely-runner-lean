# Transformation 4: uniform scaling rho -> lam*rho.
# Part A: cascade on raw readings, start R'_0 = 1/min (the code's convention): states scale exactly, R'_i = R_i/lam.
# Part B: cascade with the start FIXED at R' = 1 on raw readings lam*rho (rho_1=1): equals the cascade of rho started at R = lam.  Which lam give the same landing / path?
import sys; sys.path.insert(0, '.')
from equiv_lib_v1 import *
from collections import Counter, defaultdict
def path_from(rhos, R):
    steps = []
    while True:
        bl = [i for i, r in enumerate(rhos) if blocks(R, r)]
        if not bl: return steps, R
        ex = [((8 * round(R * rhos[i] / 8) + 1) / rhos[i], i, round(R * rhos[i] / 8)) for i in bl]
        R2, setter, lap = max(ex); steps.append(dict(R=R, setter=setter, lap=lap, R2=R2)); R = R2
arrs, rnd = pool(4004, 2500)
lams = [F(1, 4), F(1, 2), F(3, 4), F(9, 10), F(1), F(11, 10), F(5, 4), F(3, 2), F(2), F(3), F(5), F(7), F(8), F(9), F(10), F(17, 2), F(16), F(17), F(100, 7)]
# Part A
nA = okA = okAo = 0
for a in arrs:
    ia = ident(a)
    for lam in rnd.sample(lams + [F(rnd.randint(1, 60), rnd.randint(1, 12)) for _ in range(3)], 4):
        b = [lam * r for r in a]; ib = ident(b); nA += 1
        okA += all(y * lam == x for x, y in zip(ia['S'], ib['S'])) and len(ia['S']) == len(ib['S']) and ia['I'] == ib['I']
        okAo += (full(b)['path'] == full(a)['path'] and full(b)['R'] == full(a)['R'])
print("PART A: path(lam*rho) from start 1/min(lam*rho): trials", nA, "; states_i(lam*rho)*lam == states_i(rho) and identity path equal:", okA, "; normalised outcome() path and R* equal:", okAo)
# Part B
res = defaultdict(Counter); bad = {}
for a in arrs:
    steps0, R0 = path(a); S0 = [s['R'] for s in steps0] + [R0]; P0 = [(s['setter'], s['lap']) for s in steps0]
    for lam in lams:
        st, Rl = path_from(a, lam)           # == fixed start R'=1 for raw readings lam*a, R = lam*R'
        Sl = [s['R'] for s in st] + [Rl]
        same_L = (Rl == R0); on_chain = lam in S0
        tag = "lam<1" if lam < 1 else ("lam=1" if lam == 1 else "lam>1")
        c = res[(lam)]; c['n'] += 1; c['L equal'] += same_L; c['path-tail equal (suffix of original)'] += (Sl == S0[S0.index(lam):]) if on_chain else 0
        c['lam on original chain'] += on_chain; c['lonely at start (no move)'] += (len(st) == 0)
        c['merges (L equal) though lam not on chain'] += (same_L and not on_chain)
        if lam != 1 and not same_L and (lam not in bad or cx_key(a) < bad[lam][0]): bad[lam] = (cx_key(a), a, S0, Sl)
        # invariant: lam=1 identical
print("\nPART B: fixed start R'=1 on raw lam*rho  == cascade of rho (rho_1=1) started at R=lam; landing in rho units compared with R*; %d arrangements per row" % len(arrs))
print("%-8s %6s %10s %12s %14s %18s" % ("lam", "n", "L equal", "lam on chain", "lonely-at-start", "merge,off-chain"))
for lam, c in res.items():
    print("%-8s %6d %10d %12d %14d %18d" % (lam, c['n'], c['L equal'], c['lam on original chain'], c['lonely at start (no move)'], c['merges (L equal) though lam not on chain']))
print("\nSmallest counterexamples (landing differs), per lam:")
for lam, (k, a, S0, Sl) in sorted(bad.items()):
    print("  lam=%s rho=%s  chain from R=1: %s -> R*=%s ; chain from R=lam: %s -> %s" % (lam, fmt(a), [str(x) for x in S0[:-1]], S0[-1], [str(x) for x in Sl[:-1]], Sl[-1]))

# Part C: lam<1 (start R=lam<1 in rho units, zones with j=0 and j>=1 can block): search for a landing different from R*, including targeted arrangements
# with a reading in (7/lam, 9/lam) or (15/lam, 17/lam) (blocking at R=lam in a lap-1/lap-2 zone) and readings placed between R=lam and R=1 zone entries.
rndC = random.Random(4040); nC = viol = 0; vio_ex = []; byk = Counter()
for t in range(12000):
    lam = F(rndC.randint(1, 99), 100)
    a = gen(rndC)
    if t % 2:                      # targeted: put a reading just inside (8j-1, 8j+1)/lam for a lap j in {1,2}
        j = rndC.choice((1, 2)); y = rndC.randint(1, 6)
        a = list(a); a[y] = q(float((8 * j - 1) / lam + (F(2) / lam) * F(rndC.randint(1, 999), 1000)), 1000)
        a = sorted(set(norm(a)))
        if len(a) != 7 or a[1] <= 1: continue
    steps0, R0 = path(a); st, Rl = path_from(a, lam); nC += 1
    k = len(st); byk[k] += 1
    if Rl != R0:
        viol += 1; vio_ex.append((cx_key(a), a, lam, [str(s_['R']) for s_ in steps0], R0, [str(s_['R']) for s_ in st], Rl))
print("\nPART C: lam<1 (start R=lam), trials", nC, "; landing differs from R*:", viol, "; moves taken by the lam-start chain:", sorted(byk.items()))
vio_ex.sort(key=lambda x: x[0])
for e in vio_ex[:3]: print("  smallest violation: rho=%s lam=%s ; chain from R=1 %s -> %s ; chain from R=lam %s -> %s" % (fmt(e[1]), e[2], e[3], e[4], e[5], e[6]))

# Part D: landing(s) = first unblocked R >= s (right end of the component of the union of open zones containing s).  Independent sweep vs the chain, and the exact start rule L(s)=R* iff s<=R*.
def sweep_first_unblocked(rhos, s, bound):
    zs = []
    for r in rhos:
        j = 0
        while True:
            lo, hi = F(8 * j - 1) / r, F(8 * j + 1) / r
            if lo >= bound: break
            if hi > s: zs.append((max(lo, F(0)), hi))
            j += 1
    zs.sort(); cur = s
    # cur is unblocked iff no zone strictly contains it
    changed = True
    while changed:
        changed = False
        for lo, hi in zs:
            if lo < cur < hi: cur = hi; changed = True
    return cur
rndD = random.Random(4050); nD = okD = 0; nE = okE = 0; pair = Counter()
for a in arrs[:1200]:
    steps0, R0 = path(a)
    for s in [F(1, 3), F(1), (R0 + 1) / 2, R0, R0 + F(1, 100), R0 + F(1), F(rndD.randint(1, 4000), 100)]:
        st, Rl = path_from(a, s); sw = sweep_first_unblocked(a, s, Rl + 1)   # bound only truncates the zone list; the answer is read off the sweep
        nD += 1; okD += (sw == Rl)
        pair[(Rl == R0, s <= R0)] += 1
print("\nPART D: chain landing from start s == independent sweep (first unblocked point >= s):", okD, "of", nD)
print("        (landing equals R*, start s <= R*) counts:", dict(pair), " -> L(s)=R* iff s<=R* has violations:", pair[(True, False)] + pair[(False, True)])
