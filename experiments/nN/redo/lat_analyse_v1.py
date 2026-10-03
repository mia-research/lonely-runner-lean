# Analysis of lat_state2_s*_v1.pkl (+ lat_state_m1_v1.pkl cross-check). Exact; decimals are integer-division renderings of exact fractions.
import pickle, glob, sys
from fractions import Fraction as F
from math import isqrt
K = pickle.load(open('lat_known_paths_v1.pkl','rb'))
def dec(x, d=6):
    x = F(x); n = x.numerator * 10**d // x.denominator
    return "%d.%0*d" % (n // 10**d, d, n % 10**d)
def divisors(n):
    ds = []; i = 1
    while i * i <= n:
        if n % i == 0: ds.append(i); ds.append(n // i)
        i += 1
    return ds
def formula(R, cmax=120):
    out = []
    for c in range(1, cmax):
        T = R * (8*c-1)**2 / 9
        if T.denominator != 1: continue
        T = int(T)
        for d in divisors(T):
            if d % 8 == 1 and (T // d) % 8 == 1 and d <= T // d: out.append(((d-1)//8, (T//d-1)//8, c))
    return out
def stair(R):
    best = None
    for k in range(0, 40):
        v = 7 * F(7, 9) ** k
        if best is None or abs(R - v) < abs(R - best[1]): best = (k, v)
    return best
S = sys.argv[1:] or sorted(int(f.split('_s')[1].split('_')[0]) for f in glob.glob('lat_state2_s*_v1.pkl'))
allwords = {}
rep = []
for s in map(int, S):
    st = pickle.load(open('lat_state2_s%d_v1.pkl' % s, 'rb')); rec = st['rec']; D = st['doneM']
    rep.append("\n## s = %d (readings a/%d, gcd(a)=1, a_1=%d, a_7 <= %d; exhaustive over this family: a_7 from %d to %d)" % (s, s, s, D, s+6, D))
    tot = sum(r['n'] for r in rec.values()); sk = sum(r['skipped'] for r in rec.values())
    rep.append("arrangements computed %d (skipped for gcd>1: %d); total %d" % (tot, sk, tot+sk))
    Ns = [N for N in range(12, 400, 4) if s*N <= D]
    if D % s == 0 and D//s not in Ns: Ns.append(D//s)
    prev = {}
    seen = {k: set() for k in ('land','pair','cls','word','free','red')}
    cum = {k: {} for k in seen}
    rep.append("\n| N (a7 <= sN) | rho_7<= | arrangements | landing values | max R* | pairs | classes | words | lap-free | reduced | words not in J2 set | +land | +pair | +cls | +word | +free | +red | +newword |\n|"+"---|"*18)
    lastM = s + 4
    newwords = {}
    prevc = dict(land=0,pair=0,cls=0,word=0,free=0,red=0,nw=0)
    for N in Ns:
        for M in range(lastM + 1, s*N + 1):
            if M not in rec: continue
            r = rec[M]
            for k in seen:
                for key, ks in r[k].items(): cum[k].setdefault(key, ks)
            for w, ks in r['newword'].items(): newwords.setdefault(w, ks)
        lastM = s*N
        n = sum(rec[M]['n'] for M in range(s+5, s*N+1) if M in rec)
        mx = max(cum['land']); c = dict(land=len(cum['land']), pair=len(cum['pair']), cls=len(cum['cls']), word=len(cum['word']), free=len(cum['free']), red=len(cum['red']), nw=len(newwords))
        rep.append("| %d | %d | %d | %d | %s (%s) | %d | %d | %d | %d | %d | %d | %s |" % (N, N, n, c['land'], mx, dec(mx), c['pair'], c['cls'], c['word'], c['free'], c['red'], c['nw'], " | ".join("+%d" % (c[k]-prevc[k]) for k in ('land','pair','cls','word','free','red','nw'))))
        prevc = c
    # hole check: words from arrangements with rho_7 <= 17 not in J2
    hole = {}
    for M, r in rec.items():
        if M <= 17*s:
            for w, ks in r['newword'].items(): hole.setdefault(w, ks)
    rep.append("\nHole check (rho_7 <= 17, a7 <= %d): distinct path words not in the J2 known set: %d %s" % (17*s, len(hole), list(hole.items())[:3]))
    # known-set coverage by this family (rho_7<=17)
    inJ2 = set(w for M, r in rec.items() if M <= 17*s for w in r['word'] if w in K['J2'])
    rep.append("J2 known paths reached by this family with rho_7<=17: %d of %d" % (len(inJ2), len(K['J2'])))
    nw = {w: ks for M, r in rec.items() for w, ks in r['newword'].items()}
    rep.append("Words not in J2 (all a7 in family): %d; arrangements whose word is in J2: %d of %d" % (len(nw), sum(r['known_n'] for r in rec.values()), tot))
    for w, ks in nw.items(): allwords.setdefault(w, (s, ks))
    tops = sorted((x for r in rec.values() for x in r['top']), reverse=True)[:5]
    rep.append("max R* = %s = %s ; ratio to 4s = %s (decimal %s); landing > 7: %d arrangements" % (tops[0][0], dec(tops[0][0]), tops[0][0]/(4*s), dec(tops[0][0]/(4*s)), sum(r['gt7_n'] for r in rec.values())))
    rep.append("Top five (readings a_i with s=a_1):")
    for R, ks in tops:
        k, v = stair(R)
        rep.append("  R*=%s (%s) ks=%s ; nearest 7(7/9)^k: k=%d value %s ratio R*/value %s ; 9(8a+1)(8b+1)/(8c-1)^2 solutions (a,b,c<120 search): %s" % (R, dec(R), ks, k, dec(v), dec(R/v), formula(R)[:4]))
    cr = sorted((R, ks) for r in rec.values() for R, ks in r['gt7'])[:5]
    rep.append("Landing > 7 smallest-a7 examples: %s" % cr)
    nm = sorted((ks[-1], ks) for r in rec.values() for ks in r['nomove'])[:5]
    rep.append("No-move (lonely at R=1) count %d; first examples: %s" % (sum(r['nomove_n'] for r in rec.values()), [x[1] for x in nm]))
    rep.append("Violations: closer==opener with opener rank != 7: %d ; gate (landing>7 iff rank 1 sets a move): %d" % (sum(len(r['viol_oc']) for r in rec.values()), sum(len(r['viol_gate']) for r in rec.values())))
    nh = {}
    for r in rec.values():
        for k2, v in r['nm_hist'].items(): nh[k2] = nh.get(k2, 0) + v
    rep.append("moves histogram: %s" % sorted(nh.items()))
    top3 = {}
    for r in rec.values():
        pass
P=set(); Wd={}
for s in map(int,S):
    st=pickle.load(open('lat_state2_s%d_v1.pkl'%s,'rb'))
    for M,r in st['rec'].items():
        P|=set(r['pair'])
        for w,ks in r['word'].items(): Wd.setdefault(w,set()).add(s)
rep.append("\nUnion over s=%s of (opener rank, closer rank) pairs: %d: %s" % (S,len(P),sorted(P,key=lambda x:(x[0] or 0,x[1]))))
rep.append("Path words total over s=%s: %d; words occurring in more than one s: %d; words only in s=2 and not in J2: %d; only in s=3 not in J2: %d" % (S,len(Wd),sum(1 for v in Wd.values() if len(v)>1),sum(1 for w,v in Wd.items() if v=={2} and w not in K['J2']),sum(1 for w,v in Wd.items() if v=={3} and w not in K['J2'])))
rep.append("Words in s=2 (rho_7 in (17,22]) not in J2 and not in s=1 words: %d" % sum(1 for w,v in Wd.items() if 2 in v and 1 not in v and w not in K['J2']))
rep.append("\n## Cross-family: words not in J2 across the listed s: %d distinct (first occurrence s,example kept)" % len(allwords))
open('lat_analysis_v1.out', 'w').write("\n".join(rep)); print("\n".join(rep))
