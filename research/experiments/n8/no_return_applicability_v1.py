"""How often does `no_return_after_few_faster` actually apply, and would a larger `g` buy anything?

`no_return_tightness_v1.py` shows the shipped hypothesis `2g+2 <= n` is TIGHT as a P-uniform statement
(sharp limit 3 at n=8) but loose at small laps: sharp allows g <= 7 at P = 0 and g <= 4 at P = 1.

Whether that is worth proving depends on how often the theorem's OTHER hypothesis holds. It needs

    hlap : for all intervening j, P + 1 <= Q j          ("the intervening moves are faster")

where P is the lap at which the returning runner last set. This measures, on real cascades:

  (a) consistency -- no observed return may satisfy (gap <= 3 AND hlap), since the theorem forbids it;
  (b) applicability -- of the returns that DO occur, how many satisfy hlap at all, and how many extra
      would be excluded if g rose from 3 to the sharp P-dependent bound.

A return that fails hlap is untouched by the theorem at ANY g, so it bounds what raising g can buy.
"""
import sys, random
from fractions import Fraction as F
from collections import Counter

n = 8; INV_N = F(1, n)
def fract(x):   return x - (x.numerator // x.denominator)
def cd(x):      return min(fract(x), 1 - fract(x))
def inWay(d,t): return cd(d * t) < INV_N
def ceil_(x):   return -((-x.numerator) // x.denominator)
def nxt(d,t):   return (F(ceil_(d * t - INV_N)) + INV_N) / d
def move(ds,t):
    acc = t
    for d in ds:
        if inWay(d, t):
            o = nxt(d, t)
            if o > acc: acc = o
    return acc

def trace(dsi, maxsteps=2000):
    ds = sorted(F(d) for d in dsi); m = min(ds); t = F(1) / (n * m); out = []
    for _ in range(maxsteps):
        t2 = move(ds, t)
        if t2 == t: return out
        setter = next(d for d in ds if inWay(d, t) and nxt(d, t) == t2)
        out.append((setter, ceil_(setter * t - INV_N)))
        t = t2
    return None

def sharp_g(P):
    """largest g with F^g <= (P+1-h)/(P+h), h = 1/8 -- from no_return_tightness_v1"""
    h = F(1, n); fac = (F(P) + 1 + h) / (F(P) + 1 - h); tgt = (F(P) + 1 - h) / (F(P) + h)
    g = 0; cur = F(1)
    while g < 40:
        cur2 = cur * fac
        if cur2 > tgt: return g
        cur = cur2; g += 1
    return 40

def analyse(tr):
    """returns list of (gap, P, hlap_holds) for every return in the trace"""
    pos = {}
    for i, (s, P) in enumerate(tr): pos.setdefault(s, []).append((i, P))
    res = []
    for s, lst in pos.items():
        for (i, P), (j, _) in zip(lst, lst[1:]):
            inter = tr[i+1:j]
            hlap = all(Q >= P + 1 for _, Q in inter)
            res.append((j - i - 1, P, hlap))
    return res

CASES = [("section 6.7 climb", [49,205,234,256,286,323,366]),
         ("section 6.9 row",   [30,74,96,127,159,175,224])]
NSAMP = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
random.seed(20260917)

print(f"n = {n}: applicability of no_return_after_few_faster on real cascades\n")
allret = []
for name, dsi in CASES:
    tr = trace(dsi); rets = analyse(tr); allret += rets
    viol = [(g,P) for g,P,h in rets if h and g <= 3]
    print(f"  {name}: {len(tr)} moves, {len(rets)} returns")
    print(f"     returns satisfying hlap (all intervening laps >= P+1): "
          f"{sum(1 for _,_,h in rets if h)}/{len(rets)}")
    print(f"     CONSISTENCY -- returns with hlap AND gap <= 3 (theorem forbids these): {len(viol)}"
          f"   {'OK' if not viol else 'VIOLATION ' + str(viol)}")
    extra = [(g,P) for g,P,h in rets if h and 3 < g <= sharp_g(P)]
    print(f"     extra returns a sharp P-dependent g would exclude: {len(extra)}  {extra}")
    print()

for _ in range(NSAMP):
    while True:
        dsi = random.sample(range(1, 201), 7); m = min(dsi)
        if max(dsi) <= 8 * m: break
    tr = trace(dsi)
    if tr: allret += analyse(tr)

tot = len(allret); hl = [r for r in allret if r[2]]
viol = [(g,P) for g,P,h in allret if h and g <= 3]
extra = [(g,P) for g,P,h in allret if h and 3 < g <= sharp_g(P)]
print(f"  --- pooled over the named cases plus {NSAMP} shuffled arrangements ---")
print(f"  returns observed: {tot}")
print(f"  satisfying hlap:  {len(hl)}  ({100*len(hl)/tot:.1f}%)  <- the theorem's reach at ANY g")
print(f"  CONSISTENCY: observed returns with hlap and gap <= 3: {len(viol)}"
      f"   {'OK (theorem holds on every cascade seen)' if not viol else 'VIOLATION'}")
print(f"  extra excluded by the sharp P-dependent g: {len(extra)}")
if hl:
    print(f"  gap histogram among hlap returns: {dict(sorted(Counter(g for g,_,_ in hl).items()))}")
    print(f"  P histogram among hlap returns:   {dict(sorted(Counter(P for _,P,_ in hl).items()))}")
