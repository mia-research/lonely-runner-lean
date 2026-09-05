"""Independent cross-check: predict g=2 from the exhibited identity, confirm with the CENSUS's own
deg_gcd over F_l.  Random (e1,p) integers, both eps branches, plus off-relation negatives."""
import random, sys
sys.path.insert(0,"/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
import run_n1_120deg_v1 as R
import audit_n1_vsign_v2_core as core

random.seed(20260801)
l = 1000003
assert core.is_prime(l) and (l-1) % 3 == 0
w = R.primitive_root_of_order(3, l)
assert pow(w,3,l)==1 and w!=1

def g_of(e1,e2,e3,e4):
    L  = [e4 % l, (-e3) % l, e2 % l, (-e1) % l, 1]
    Lz = [L[k]*pow(w,k,l) % l for k in range(5)]
    return R.deg_gcd(L, Lz, l)

ok = True
for eps in (+1,-1):
    hits = []
    for _ in range(400):
        e1 = random.randrange(1, l); p = random.randrange(2, 10**6)
        e2 = (e1*e1 - eps*p) % l                      # ON the relation
        g  = g_of(e1, e2, eps*p*e1, p*p)
        hits.append(g)
    print("eps=%+d  ON-relation  g values seen: %s  -> %s" % (eps, sorted(set(hits)),
          "ALL g>=2" if min(hits)>=2 else "*** BROKEN ***"))
    if min(hits) < 2: ok = False
    neg = []
    for _ in range(400):
        e1 = random.randrange(1, l); p = random.randrange(2, 10**6)
        d  = random.choice([1,2,-1,-3,7])
        e2 = (e1*e1 - eps*p + d) % l                  # OFF the relation
        neg.append(g_of(e1, e2, eps*p*e1, p*p))
    frac2 = sum(1 for g in neg if g>=2)
    print("eps=%+d  OFF-relation g>=2 in %d/400  (must be ~0: else the identity is vacuous)" % (eps, frac2))
    if frac2 > 5: ok = False
print("CROSS-CHECK:", "PASS" if ok else "*** FAIL ***")
