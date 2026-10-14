"""Does the product of pairwise conditionals actually BOUND the joint density?

For a chain b1|b2|...|b5|m, q mod b5 DETERMINES q mod b4,...,q mod b1.  So the conditions are not
independent conditionals.  The claim to test is the telescoping inequality

    density(m; b1..b5)  >=  (|I(m)|/m) * prod_i cond(b_i, b_{i+1})     with b6 = m.

If it fails, the product argument is unsound and must not be used.
"""
from fractions import Fraction as F

def I(b): return (-(-(b-1)//8), (7*b-1)//8)
def cond(b, bp):
    lo, hi = I(bp); lo2, hi2 = I(b)
    return F(sum(1 for r in range(lo, hi+1) if lo2 <= r % b <= hi2), hi-lo+1)
def density(m, bs):
    c = [(b,)+I(b) for b in bs] + [(m,)+I(m)]
    return F(sum(1 for q in range(m) if all(lo<=q%b<=hi for b,lo,hi in c)), m)
def chains(m):
    ds = sorted(d for d in range(2,m) if m%d==0); out=[]
    def go(p):
        if len(p)==5: out.append(tuple(p)); return
        last = p[-1] if p else 1
        for d in ds:
            if d>last and d%last==0: go(p+[d])
    go([]); return out

tot = viol = 0; worst = None
for m in range(24, 800):
    for ch in chains(m):
        tot += 1
        lo, hi = I(m)
        prod = F(hi-lo+1, m)
        seq = list(ch) + [m]
        for i in range(len(ch)):
            prod *= cond(seq[i], seq[i+1])
        d = density(m, list(ch))
        r = d / prod
        if d < prod: viol += 1
        if worst is None or r < worst[0]: worst = (r, m, ch, d, prod)
print(f"chain profiles m < 800 : {tot:,}")
print(f"  telescoping inequality  density >= (|I(m)|/m) * prod cond  VIOLATED in {viol:,} cases")
print(f"  tightest ratio density/product = {float(worst[0]):.4f}  at m={worst[1]} chain={worst[2]}")
print(f"     density {worst[3]} = {float(worst[3]):.6f}   product {worst[4]} = {float(worst[4]):.6f}")
print()
if viol:
    print("  => the product argument is UNSOUND as stated and must not be used.")
else:
    print("  => the inequality holds on every chain tested; still an empirical claim, not a proof.")
