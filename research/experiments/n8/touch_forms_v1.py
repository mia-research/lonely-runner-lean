#!/usr/bin/env python3
"""touch_forms_v1.py  (Task AI)  -- exact, integers and Fractions only.

MODEL.  Disparity set S of positive reals d_1..d_7, eight runners incl. subject.
Lonely at t: frac(d t) in [1/8,7/8] for all d in S.  A TOUCH is an isolated point
t0 of the lonely set.  Its critical runners: openers O (frac = 1/8) and entries
E (frac = 7/8); both nonempty at an isolated point (if E empty the lonely set
continues to the right; if O empty it continues to the left).
First order under d_i -> d_i + e*delta_i, t0 -> t0 + e*tau:
   opener i:  delta_i t0 + d_i tau >= 0 ;  entry j:  delta_j t0 + d_j tau <= 0.
tau exists iff  max_{i in O}(-x_i) <= min_{j in E}(-x_j)  with x = delta/d, i.e.
   C_tau = { x : x_i >= x_j  for all i in O, j in E }.
EXACT COVERAGE TEST.  C_tau depends on x only through the weak order of x.  A
point x violating a touch has a STRICT inequality x_i < x_j, which survives a
small perturbation; hence a violator of all touches exists iff a STRICT TOTAL
ORDER (permutation of the 7 positions) violates all touches.  We test all 5040
permutations: perm p is covered by touch (O,E) iff min_{O} p > max_{E} p.
Certificate: coverage = the 5040-permutation table (a minimal sub-family of
touches covering is reported); violation = the uncovered permutation, delta_i =
rank_i * d_i.
Method statement: no LP is needed; the Gordan/Farkas alternative reduces to a
finite combinatorial check on weak orders (exact, 5040 cases for 7 runners).

ENUMERATION (c),(d).  S (integers, set U = [lo,hi]) is touch-only iff for every
candidate time t=(8k+1)/(8a) (a in U, 0<k<... , 0<t<1) with S inside L(t) (all
frac in [1/8,7/8]) we have S meets O(t) and S meets E(t) [a lonely point with
O empty is in a positive-width piece, whose left end is itself a candidate with
E empty or is a right end; equivalence argued in the report].  Equivalently S is
contained in no bad set L(t)\\O(t), L(t)\\E(t).  Done by a C DFS (exact integer
arithmetic); each survivor is re-verified in Python by an independent
interval-intersection computation with Fractions.
Rational sets a/Q: speeds scale by Q, lonely sets scale time by 1/Q; so the
population is integer sets in [Q,12Q].
"""
import sys, os, subprocess, itertools, random, math, tempfile
from fractions import Fraction as F
from functools import lru_cache

HERE = os.path.dirname(os.path.abspath(__file__))
SCR = os.environ.get("TF_SCRATCH", tempfile.gettempdir())

# ---------------------------------------------------------------- C enumerator
CSRC = r'''
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef long long ll; typedef unsigned long long ull;
static ll gcdll(ll a, ll b){ while(b){ ll t=a%b;a=b;b=t;} return a<0?-a:a; }
int lo,hi,n; int nb=0; ull *bad;
ll *tn,*td; int nt=0; ull *Lm,*Om,*Em;
ull *alive[9]; int na[9];
int sel[8]; long long cnt=0, surv=0;
void dfs(int depth,int start,ull mask){
  if(depth==7){
    cnt++;
    int bad_any=0;
    for(int i=0;i<na[7];i++){ if((bad[alive[7][i]]&mask)==mask){bad_any=1;break;} }
    // alive[7] already filtered: any entry means bad superset
    if(na[7]==0){ surv++; for(int i=0;i<7;i++) printf("%d ",lo+sel[i]); printf("\n"); }
    return;
  }
  for(int i=start;i<n;i++){
    ull bit=1ULL<<i;
    int m=0;
    for(int k=0;k<na[depth];k++){ if(bad[alive[depth][k]]&bit) alive[depth+1][m++]=alive[depth][k]; }
    na[depth+1]=m; sel[depth]=i;
    if(n-i-1 < 6-depth){ continue; }
    dfs(depth+1,i+1,mask|bit);
  }
}
int main(int argc,char**argv){
  lo=atoi(argv[1]); hi=atoi(argv[2]); n=hi-lo+1;
  tn=malloc(sizeof(ll)*200000); td=malloc(sizeof(ll)*200000);
  Lm=malloc(8*200000);Om=malloc(8*200000);Em=malloc(8*200000);
  for(int a=lo;a<=hi;a++) for(int k=0;k<a;k++){
    ll num=8LL*k+1, den=8LL*a; ll g=gcdll(num,den); num/=g;den/=g;
    int dup=0; for(int j=0;j<nt;j++) if(tn[j]==num&&td[j]==den){dup=1;break;}
    if(dup) continue; tn[nt]=num;td[nt]=den;nt++;
  }
  bad=malloc(8*2*nt+16);
  for(int j=0;j<nt;j++){
    ull L=0,O=0,E=0;
    for(int a=lo;a<=hi;a++){
      ll num=a*tn[j], den=td[j]; ll r=((num%den)+den)%den;
      if(8*r>=den && 8*r<=7*den) L|=1ULL<<(a-lo);
      if(8*r==den) O|=1ULL<<(a-lo);
      if(8*r==7*den) E|=1ULL<<(a-lo);
    }
    bad[nb++]=L&~O; bad[nb++]=L&~E;
  }
  for(int d=0;d<=8;d++) alive[d]=malloc(8*(nb+4));
  for(int i=0;i<nb;i++) alive[0][i]=i; na[0]=nb;
  dfs(0,0,0);
  fprintf(stderr,"%d %d %d %lld %lld\n",lo,hi,nb,cnt,surv);
  return 0;
}
'''
# NOTE on the C pruning: alive[depth] holds indices of bad sets containing all
# chosen elements so far; at depth 7 a survivor has an empty list.

def build_c():
    src = os.path.join(SCR, "tf_enum.c"); exe = os.path.join(SCR, "tf_enum")
    open(src, "w").write(CSRC)
    subprocess.check_call(["cc", "-O2", "-o", exe, src])
    return exe

def enum_touch_only(exe, lo, hi):
    p = subprocess.run([exe, str(lo), str(hi)], capture_output=True, text=True, check=True)
    sets = [tuple(map(int, l.split())) for l in p.stdout.strip().split("\n") if l.strip()]
    return sets, p.stderr.strip()

# ------------------------------------------------------- independent exact lonely set
def runner_intervals(d, T):
    """closed intervals [(k+1/8)/d,(k+7/8)/d] meeting [0,T]"""
    d = F(d); out = []
    k = 0
    while True:
        a = (k + F(1, 8)) / d
        if a > T: break
        out.append((a, min((k + F(7, 8)) / d, T)))
        k += 1
    return out

def lonely_components(S, T=F(1)):
    cur = runner_intervals(S[0], T)
    for d in S[1:]:
        nxt = []
        iv = runner_intervals(d, T)
        i = j = 0
        while i < len(cur) and j < len(iv):
            a = max(cur[i][0], iv[j][0]); b = min(cur[i][1], iv[j][1])
            if a <= b: nxt.append((a, b))
            if cur[i][1] < iv[j][1]: i += 1
            else: j += 1
        cur = nxt
    return cur  # sorted disjoint closed intervals (components may touch? merged below)

def frac(x): return x - (x.numerator // x.denominator)

def crit(S, t):
    O = [i for i, d in enumerate(S) if frac(F(d) * t) == F(1, 8)]
    E = [i for i, d in enumerate(S) if frac(F(d) * t) == F(7, 8)]
    return O, E

def touches_of(S, T=F(1)):
    """(touches, positive-width components); touches = list of (t0,O,E) position lists"""
    comps = lonely_components(S, T)
    pts = [c[0] for c in comps if c[0] == c[1]]
    wide = [c for c in comps if c[0] < c[1]]
    th = []
    for t0 in pts:
        O, E = crit(S, t0)
        th.append((t0, O, E))
    return th, wide

# ---------------------------------------------------------------- cones / coverage
PERMS = list(itertools.permutations(range(1, 8)))
FULL = (1 << len(PERMS)) - 1

@lru_cache(maxsize=None)
def covered_bits(Om, Em):
    O = [i for i in range(7) if Om >> i & 1]; E = [i for i in range(7) if Em >> i & 1]
    b = 0
    for idx, p in enumerate(PERMS):
        if min(p[i] for i in O) > max(p[j] for j in E): b |= 1 << idx
    return b

def mask(L):
    m = 0
    for i in L: m |= 1 << i
    return m

def coverage(touches):
    acc = 0
    for (_, O, E) in touches: acc |= covered_bits(mask(O), mask(E))
    return acc

def uncovered_perm(touches):
    acc = coverage(touches); miss = FULL & ~acc
    if miss == 0: return None
    idx = (miss & -miss).bit_length() - 1
    return PERMS[idx]

def min_cover(touches):
    """smallest sub-family of touches covering all permutations (exact, brute force by size)"""
    bits = [covered_bits(mask(O), mask(E)) for (_, O, E) in touches]
    for r in range(1, len(touches) + 1):
        for c in itertools.combinations(range(len(touches)), r):
            a = 0
            for i in c: a |= bits[i]
            if a == FULL: return c
    return None

def fmt_touch(S, tch):
    t0, O, E = tch
    return "t0=%s O=%s E=%s" % (t0, [S[i] for i in O], [S[i] for i in E])

# ------------------------------------------------- perturbation test (first-order check)
def lonely_pts_near(speeds, c, w):
    """exact lonely instants of the arrangement in [c-w,c+w]: only left ends (k+1/8)/d are
    candidates for a lonely point that is a component's left end; for isolated points
    the point is a left end.  Returns sorted list of lonely candidate left ends in the window."""
    out = set()
    for d in speeds:
        d = F(d)
        k0 = max(0, math.floor((c - w) * d - F(1, 8)) - 1)
        k = k0
        while True:
            t = (k + F(1, 8)) / d
            if t > c + w: break
            if t >= c - w:
                if all(F(1, 8) <= frac(F(e) * t) <= F(7, 8) for e in speeds): out.add(t)
            k += 1
    return sorted(out)

def least_lonely(speeds, Tmax):
    cand = set()
    for d in speeds:
        d = F(d); k = 0
        while (k + F(1, 8)) / d <= Tmax:
            cand.add((k + F(1, 8)) / d); k += 1
    for t in sorted(cand):
        if all(F(1, 8) <= frac(F(e) * t) <= F(7, 8) for e in speeds): return t
    return None

def first_order_check(S, trials, seed, eps=F(1, 10**6)):
    """for random integer delta: predicted-surviving touches (strict first order, x=delta/d
    with all pairs strict) vs touches having a lonely instant within 20*eps*(|tau|bound)."""
    rnd = random.Random(seed)
    th, _ = touches_of(S)
    agree = 0; tot = 0; bad = []
    for _ in range(trials):
        delta = [rnd.randint(-9, 9) for _ in S]
        x = [F(delta[i], S[i]) for i in range(7)]
        if len(set(x)) < 7: continue
        sp = [F(S[i]) + eps * delta[i] for i in range(7)]
        for (t0, O, E) in th:
            pred = all(x[i] > x[j] for i in O for j in E)
            predv = any(x[i] < x[j] for i in O for j in E)
            if not pred and not predv: continue
            # window: tau range is bounded by max |delta_i t0 / d_i| ; take width 20*eps*max|x|*(t0+1)
            w = 20 * eps * (max(abs(v) for v in x) * (t0 + 1))
            near = lonely_pts_near(sp, t0, w)
            actual = len(near) > 0
            tot += 1
            if actual == pred: agree += 1
            else: bad.append((delta, t0, pred, actual))
    return agree, tot, bad

# ---------------------------------------------------------------------- reports
def report_set(S, label, tau_checks=True):
    S = tuple(S)
    th, wide = touches_of(S)
    print("--- %s  S=%s  gcd=%d" % (label, S, math.gcd(*S)))
    print("    lonely components in [0,1]: %d isolated points, %d positive-width" % (len(th), len(wide)))
    for tch in th: print("    touch:", fmt_touch(S, tch))
    for w in wide: print("    wide component: [%s, %s]" % w)
    miss = uncovered_perm(th)
    if miss is None:
        mc = min_cover(th)
        print("    COVER: all 5040 strict orders of x=delta/d satisfy some touch form. minimal covering touches:",
              [fmt_touch(S, th[i]) for i in mc])
    else:
        delta = [miss[i] * S[i] for i in range(7)]
        print("    VIOLATION: order ranks=%s  delta=%s (delta_i = rank_i*d_i)" % (miss, delta))
        for e in (F(1, 100), F(1, 1000), F(1, 10**5)):
            sp = [F(S[i]) + e * delta[i] for i in range(7)]
            L = least_lonely(sp, F(3))
            print("      e=%s : least lonely time of perturbed set (searched t<=3) = %s" % (e, L))
    return th, wide, miss

def main():
    exe = build_c()
    print("=== (a) AP 1..7 ===")
    th, wide, miss = report_set((1, 2, 3, 4, 5, 6, 7), "AP")
    ag, tot, bad = first_order_check((1, 2, 3, 4, 5, 6, 7), 40, 1)
    print("    first-order model check (random delta, eps=1e-6): agree %d / %d, disagreements %d" % (ag, tot, len(bad)))
    print()
    print("=== (b) Agent AF sets ===")
    for S in [(1, 2, 3, 4, 5, 7, 12), (1, 4, 5, 6, 7, 11, 13)]:
        th, wide, miss = report_set(S, "AF")
        ag, tot, bad = first_order_check(S, 40, 2)
        print("    first-order model check: agree %d / %d, disagreements %d" % (ag, tot, len(bad)))
        # per-instant table 1/8,3/8,5/8,7/8
        for a in (1, 3, 5, 7):
            t = F(a, 8)
            print("      t=%s frac(d t) = %s -> %s" % (t, [str(frac(F(d) * t)) for d in S],
                  "lonely" if all(F(1, 8) <= frac(F(d) * t) <= F(7, 8) for d in S) else "not lonely"))
    print()
    print("=== (c) exhaustive: integer 7-subsets of [1,40], touch-only ===")
    sets, info = enum_touch_only(exe, 1, 40)
    print("C enumerator (lo hi nbad leaves survivors):", info)
    allc = 0; nocover = []
    results = []
    for S in sets:
        th, wide = touches_of(S)
        ok = (len(wide) == 0 and len(th) > 0)
        results.append((S, th, wide, ok))
    n_ok = sum(1 for r in results if r[3])
    print("survivors of C filter: %d ; re-verified touch-only (>=1 touch, 0 wide, Fractions): %d" % (len(sets), n_ok))
    prim = [r for r in results if r[3] and math.gcd(*r[0]) == 1]
    print("primitive (gcd 1): %d ; non-primitive: %d" % (len(prim), n_ok - len(prim)))
    for S, th, wide, ok in results:
        if not ok: print("  FILTER MISMATCH", S); continue
        miss = uncovered_perm(th)
        g = math.gcd(*S)
        print("  S=%s gcd=%d touches=%d  %s" % (S, g, len(th), "COVER" if miss is None else "VIOLATED rank=%s" % (miss,)))
    for S, th, wide, ok in results:
        if ok and math.gcd(*S) == 1 and S != (1, 2, 3, 4, 5, 6, 7):
            report_set(S, "(c) primitive")
    print()
    print("=== (d) rational sets a/Q, a/Q in [1,12], 7-subsets, ALL enumerated ===")
    for Q in (2, 3, 4, 5):
        lo, hi = Q, 12 * Q
        sets, info = enum_touch_only(exe, lo, hi)
        ver = []
        for S in sets:
            th, wide = touches_of(S)
            if len(wide) == 0 and len(th) > 0: ver.append(S)
        nonint = [S for S in ver if any(a % Q for a in S)]
        from math import comb
        print("Q=%d: population C(%d,7)=%d ; touch-only (integer sets scaled by Q + genuinely rational): %d ; with some a not divisible by Q (non-integer disparity): %d" %
              (Q, hi - lo + 1, comb(hi - lo + 1, 7), len(ver), len(nonint)))
        print("   C info:", info)
        for S in ver:
            th, wide = touches_of(S)
            print("   touch-only", S, "as a/Q =", [str(F(a, Q)) for a in S], "cover" if uncovered_perm(th) is None else "VIOLATED")
    print()
    print("=== (e) all 7-subsets of [1,Z]: positive-width cell present; touches and cone cover ===")
    for Z in (14, 18):
        tot = 0; stat = {}
        examples = {}
        for S in itertools.combinations(range(1, Z + 1), 7):
            th, wide = touches_of(S)
            if not wide: 
                stat['no_wide'] = stat.get('no_wide', 0) + 1
                continue
            tot += 1
            if not th: key = 'wide, 0 touches'
            else:
                key = 'wide, >=1 touch, cones cover' if uncovered_perm(th) is None else 'wide, >=1 touch, cones DO NOT cover'
            stat[key] = stat.get(key, 0) + 1
            examples.setdefault(key, S)
        print("Z=%d: C(%d,7)=%d sets" % (Z, Z, math.comb(Z, 7)))
        for k, v in sorted(stat.items()): print("   %-40s %d   e.g. %s" % (k, v, examples.get(k)))
    print()
    print("=== (e) exception examined: S=(1,2,3,4,5,6,11), touches 3/8 (O=3,11;E=5) and 5/8 (mirror) ===")
    S = (1, 2, 3, 4, 5, 6, 11)
    th, w = touches_of(S); m = uncovered_perm(th); dl = [m[i] * S[i] for i in range(7)]
    for e in (F(1, 1000),):
        sp = [F(S[i]) + e * dl[i] for i in range(7)]
        comps = lonely_components(sp, F(1))
        print("  violating delta=%s, e=%s : perturbed lonely components in [0,1]: %d, point-components: %d, least lonely time %s"
              % (dl, e, len(comps), sum(1 for c in comps if c[0] == c[1]), least_lonely(sp, F(2))))
    print("done")

if __name__ == "__main__":
    main()
