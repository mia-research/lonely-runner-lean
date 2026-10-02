# Transformation 5: reflection rho -> v = 2c - rho (mirror point c).  Position at R is (R*rho mod 8); blocked set B = (-1,1)+8Z is symmetric about 0.
# R*v = 2cR - R*rho, so status(v at R) = status(rho at R) for every rho iff 2cR in 8Z.  c = 4k (v = 8k - rho): R in Z/k.  c = 8m/R0 (mirror about a multiple of 8/R0): R in (R0/(2m))Z, R0 itself included.
import sys; sys.path.insert(0, '.')
from equiv_lib_v1 import *
from collections import Counter, defaultdict
rnd = random.Random(5005)
# Part A: exact statement at the single state R
nA = okA = 0; nB = okB = 0; nC = okC = 0; nD = okD = 0; badA = []
for t in range(8000):
    R0 = F(rnd.randint(1, 400), rnd.randint(1, 40)) + 1; m = rnd.randint(1, 4); rho = (16 * m / R0) * F(rnd.randint(1, 9999), 10000)
    v = 16 * m / R0 - rho
    if v <= 0: continue
    nA += 1; okA += (blocks(R0, rho) == blocks(R0, v))
    # at R' = n*R0/(2m): preserved
    n_ = rnd.randint(1, 30); Rp = n_ * R0 / (2 * m); nB += 1; okB += (blocks(Rp, rho) == blocks(Rp, v))
    # at generic R': fraction preserved
    Rg = R0 * F(rnd.randint(1001, 9999), 1000); 
    if (2 * (8 * m / R0) * Rg) % 8 != 0:
        nC += 1; okC += (blocks(Rg, rho) == blocks(Rg, v))
    # c=4k : R in Z/k
    k = rnd.randint(1, 5); rho = F(8 * k) * F(rnd.randint(1, 9999), 10000); v2 = 8 * k - rho
    if v2 > 0:
        Rz = F(rnd.randint(1, 60), k); nD += 1; okD += (blocks(Rz, rho) == blocks(Rz, v2))
print("PART A (single-state status):")
print("  v = 16m/R0 - rho, status at R0 equal:", okA, "of", nA)
print("  same v, status at R' = n*R0/(2m) equal:", okB, "of", nB)
print("  same v, status at generic R' (2cR' not in 8Z) equal:", okC, "of", nC, "(status differs in %d)" % (nC - okC))
print("  v = 8k - rho, status at R' in Z/k equal:", okD, "of", nD)
# Part B: the cascade with ONE reading reflected
arrs, rnd2 = pool(5006, 3500)
tab = defaultdict(Counter); worst = {}; stat0 = Counter(); nB2 = 0
for a in arrs:
    ia = ident(a); sts = ia['S']
    for y in range(1, 7):
        for k in rnd2.sample((1, 2, 3), 2):
            v = 8 * k - a[y]
            if v <= 1 or v in a: continue
            b = list(a); b[y] = v
            if min(b) != 1: continue
            nB2 += 1; ib = ident(b); c = cmpi(ia, ib)
            stat0[blocks(F(1), a[y]) == blocks(F(1), v)] += 1
            yin = clear_all(a[y], sts); vin = clear_all(v, sts)
            allZ = all((k * R).denominator == 1 for R in sts)       # k*R_i integer at every state
            allstat = all(blocks(R, a[y]) == blocks(R, v) for R in sts)
            cls = ("y and v clear at every original state" if yin and vin else
                   "y or v blocks somewhere; status of y and v equal at every state" if allstat else
                   "y or v blocks somewhere; status differs at some state")
            tab[cls]['n'] += 1
            for kk, val in c.items(): tab[cls][kk] += val
            tab[cls]['k*R_i integer at all states'] += allZ
            if not c['S']:
                kk3 = cx_key(a)
                if cls not in worst or kk3 < worst[cls][0]: worst[cls] = (kk3, a, y, v, k, ia, ib)
print("\nPART B: cascade with one reading y (rank>=2) replaced by 8k-rho_y, k in {1,2,3}; trials", nB2, "; status at R_0 = 1 equal:", dict(stat0))
for cls, c in tab.items():
    print(" class:", cls, "| n =", c['n'], "| states S equal %d, identity path I %d, landing L %d, opener O %d, closer C %d; k*R_i integer at all states: %d" % (c['S'], c['I'], c['L'], c['O'], c['C'], c['k*R_i integer at all states']))
for cls, (kk3, a, y, v, k, ia, ib) in worst.items():
    print("\n smallest counterexample (", cls, "): rho =", fmt(a), "y(rank)=%d -> %s (k=%d)" % (y + 1, v, k))
    print("   before: states", [str(s) for s in ia['S']], " after:", [str(s) for s in ib['S']])
# Part C: first-state mirror: v = 16m/R_0' - rho for the FIRST BLOCKED state, y blocking there; does the jump change?
nj = nsame = 0; ex = None
for a in arrs:
    steps, R = path(a)
    if not steps: continue
    R1 = steps[0]['R']
    for y in steps[0]['blockers']:
        if y == 0: continue
        for m in (1, 2):
            v = 16 * m / R1 - a[y]
            if v <= 1 or v in a: continue
            b = list(a); b[y] = v
            st2, _ = path(b); nj += 1
            same_jump = bool(st2) and st2[0]['R2'] == steps[0]['R2']
            nsame += same_jump
            if not same_jump and ex is None: ex = (a, y, v, steps[0]['R2'], st2[0]['R2'] if st2 else None)
print("\nPART C: reflecting a BLOCKER of the first state R_0 about 8m/R_0 (status at R_0 preserved by Part A): jump R_0 -> R_1 unchanged in", nsame, "of", nj, "trials")
if ex: print("   example where the jump changes: rho =", fmt(ex[0]), "y=%d -> %s; R_1 was %s, now %s" % (ex[1] + 1, ex[2], ex[3], ex[4]))
