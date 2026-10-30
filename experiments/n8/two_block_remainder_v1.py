"""E646. Two-block template (UnequalAPArrangement.speeds c A u v p, u = 1, v = b): block L = c..c+(p-1),
block R = c+A, c+A+b, ..., gap G = A-(p-1). Which (p, G, b) do the proved two-block regions cover?
Regions are copied from the class definitions (TwoBlockCoalescence.TwoBlockRegion, UnequalTwoAPBlockClass with
u = 1, GeneralTwoAPBlockClass at b = 1). Every region is upward closed in G, so the covered set at (p, b) is
G >= Gmin(p, b); the mirror (s < 0) maps (p, G, b) to (8-p, G/b, 1/b). Exact Fractions; the b list is a sample,
the thresholds at each b are exact."""
from fractions import Fraction as F
INF=None
def gmin_regions(p,b):
    c=[]
    m=max(F(1),b)
    if 2<=p<=6: c.append((21*m,'Sep21'))
    if p==2:
        c.append((9*m,'TwoSixNine'))
        if b<F(6,5): c.append((max(F(4,3),40*b/(6-5*b)),'TwoSixThin'))
    if p==3:
        c.append((F(32,3)*m,'FullThreeFive'))
        if b>=F(6,7): c.append((32*b/3,'MiddleFive'))
    if p==4:
        if b==2: c.append((F(51,4),'MixedFourTwo'))
        if 2<=b<F(8,3): c.append((max(9*b*b/(8-3*b),F(0)),'MixedFourParam'))
        if F(8,7)<=b<=2: c.append((9*b,'MixedFourLower'))
    if 2<=p<=6:
        # Unequal, u=1, v=b: G>0, 8(p-1)<=G(8-p), 8(7-p)b<=Gp, (7-p)b(1/8+1/G)<=3/4, (p-1)(1/(8b)+1/G)<=3/4
        lo=[F(8*(p-1),8-p), F(8*(7-p),p)*b]
        ok=True
        a=F(3,4)-(7-p)*b/8
        if a<=0: ok=False
        else: lo.append((7-p)*b/a)
        a2=F(3,4)-F(p-1)/(8*b)
        if a2<=0: ok=False
        else: lo.append((p-1)/a2)
        if ok: c.append((max(lo),'Unequal'))
    if b==1: c.append((F(-10**9),'GeneralTwoAP(b=1, all G)'))
    return c
def gcov(p,b):
    c=gmin_regions(p,b)+[(g*b,name+'[mirror]') for g,name in gmin_regions(8-p,1/b)]
    if not c: return None,'none'
    g,name=min(c,key=lambda x:x[0]); return g,name
bs=[F(1,8),F(1,4),F(1,2),F(2,3),F(6,7),F(1),F(8,7),F(3,2),F(2),F(7,3),F(3),F(4),F(8)]
print("p  b      Gcov (exact)       region attaining it")
for p in range(2,7):
    for b in bs:
        g,n=gcov(p,b)
        print(p,str(b).ljust(6),(str(g) if g is not None else 'uncovered for all G').ljust(18),n)
