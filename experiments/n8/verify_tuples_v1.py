"""Tasks 5+6: explicit n=8 tuples satisfying ALL hypotheses; exact-integer checks of
(a) SAFE-ness of every b in [3L/5,5L/7), (b) x_0(E)>0, (c) whether the safe fibre actually
delivers a witness k once the E_div runners are included."""
from math import gcd, lcm
from fractions import Fraction as F
from itertools import combinations
n = 8

def Sol(e,j,m): return frozenset(r for r in range(m) if (e*r-j)%m==0)
def bad(e,t,m): return Sol(e,(-t)%m,m)|Sol(e,(-(t+1))%m,m)

def hypotheses(E):
    """returns (ok, why) -- Case 2, Unit-Complete, representative speeds, gcd 1, n-1 distinct"""
    E = sorted(E)
    if len(set(E)) != n-1: return False, "not 7 distinct"
    if any(e<=0 for e in E): return False, "non-positive"
    g = 0
    for e in E: g = gcd(g,e)
    if g != 1: return False, "gcd != 1"
    Ediv = [e for e in E if e % n == 0]
    Enon = [e for e in E if e % n != 0]
    if not Ediv: return False, "not Case 2"
    # representative speeds: q_e = 0 i.e. e = rho_e, so 1 <= e <= n-1
    if any(not (1 <= e <= n-1) for e in Enon): return False, "not representative speeds"
    R = {e % n for e in Enon}
    missing = set(range(1,n)) - R
    if len(missing) != 2: return False, f"|missing|={len(missing)}"
    if any(gcd(r,n)==1 for r in missing): return False, "missing class is a unit -> not Unit-Complete"
    L = 1
    for e in E: L = lcm(L,e)
    if L % n: return False, "n does not divide L"
    if not L > 2*n: return False, "L <= 2n"
    return True, dict(Enon=Enon, Ediv=Ediv, L=L, missing=sorted(missing))

def x0_direct(E, L):
    """exact count of k in 1..N-1 with (e k mod N) in [L,(n-1)L] for all e"""
    N = n*L; hi = (n-1)*L; cnt = 0; first = None
    for k in range(1, N):
        for e in E:
            v = (e*k) % N
            if v < L or v > hi: break
        else:
            cnt += 1
            if first is None: first = k
    return cnt, first

def analyse(E):
    ok, info = hypotheses(E)
    if not ok: return None, info
    Enon, Ediv, L = info['Enon'], info['Ediv'], info['L']
    N = n*L
    a, b_end = F(3*L,5), F(5*L,7)
    bs = [x for x in range(int(a) , int(b_end)+2) if a <= x < b_end]
    rec = []
    for b in bs:
        # SAFE per the manuscript definition: union over E_non only
        Un = set()
        for e in Enon:
            t = (e*b)//L
            Un |= bad(e,t,n)
        safe = (Un != set(range(n)))
        uncovered = sorted(set(range(n))-Un)
        # in B_div?
        inBdiv = (F(L,n) <= b <= F((n-1)*L,n))
        # TRUE good r's: test k = L*r + b against the ORIGINAL definition, all runners
        good_r = []
        for r in range(n):
            k = L*r + b
            if k % N == 0: continue
            if all(L <= (e*k) % N <= (n-1)*L for e in E): good_r.append(r)
        # do the E_div runners pass at this b (their condition is r-independent)?
        div_ok = all(L <= (e*(L*0+b)) % N <= (n-1)*L for e in Ediv)  # e*L*r == 0 mod N when n|e
        rec.append(dict(b=b, safe=safe, uncovered=uncovered, inBdiv=inBdiv,
                        good_r=good_r, div_ok=div_ok))
    cnt, first = x0_direct(E, L)
    return dict(E=sorted(E), Enon=Enon, Ediv=Ediv, L=L, N=N, missing=info['missing'],
                window=(str(a),str(b_end)), recs=rec, x0=cnt, first_k=first), None

TUPLES = []
for rho in (2,4,6):
    for dv in [(8,16),(8,24),(8,32),(8,40),(16,24),(8,48),(24,40),(8,56),(16,48),(8,72),(8,120),(40,56)]:
        TUPLES.append([1,3,5,7,rho,dv[0],dv[1]])

print(f"{'E':<30}{'L':>7}{'x_0':>8}{'k*':>9}  {'#b':>3} {'safe':>5} {'inBdiv':>6} {'wit':>4} {'divOK':>6}  uncovered")
print("-"*115)
bad_tuples = []
for E in TUPLES:
    res, why = analyse(E)
    if res is None:
        print(f"{str(sorted(E)):<30}  SKIP: {why}")
        continue
    recs = res['recs']
    nsafe   = sum(r['safe'] for r in recs)
    nbdiv   = sum(r['inBdiv'] for r in recs)
    nwit    = sum(1 for r in recs if r['good_r'])
    ndivok  = sum(r['div_ok'] for r in recs)
    uncs    = sorted({tuple(r['uncovered']) for r in recs})
    flag = ""
    if nsafe != len(recs): flag += " <<SAFETY FAILS>>"
    if res['x0'] == 0:     flag += " <<x0 == 0>>"
    if nwit == 0:          flag += " <<NO WITNESS IN WINDOW>>"
    if flag: bad_tuples.append((E,res,flag))
    print(f"{str(sorted(E)):<30}{res['L']:>7}{res['x0']:>8}{str(res['first_k']):>9}  "
          f"{len(recs):>3} {nsafe:>5} {nbdiv:>6} {nwit:>4} {ndivok:>6}  {uncs}{flag}")

print("\n=== tuples with any flag ===")
if not bad_tuples: print(" none")
for E,res,flag in bad_tuples:
    print(f" {sorted(E)} L={res['L']} {flag}")
    for r in res['recs']:
        print(f"    b={r['b']:<7} safe={r['safe']!s:<6} unc={r['uncovered']} "
              f"inBdiv={r['inBdiv']!s:<6} div_ok={r['div_ok']!s:<6} good_r={r['good_r']}")
