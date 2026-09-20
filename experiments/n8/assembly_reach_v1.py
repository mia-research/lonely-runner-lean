"""Compose every PROVED sufficient condition in the framework and measure total coverage
per subject, over integer arrangements. If the disjunction is everything, the framework closes it.
  A  card <= 4 distinct |differences|        CardFour.exists_lonely_of_card_le_four
  B  card <= 6 distinct                      CardSix (integer speeds, via intLRC_seven)
  C  the first-lap window at some flank      RealDoor.doorFlank_of_window / FirstLap
  D  a flank with <= 1 non-integer ratio     Thm 6.9  (Flanks.lonely_opening_of_one_fractional)
  E  the -7 opening at some flank            MinusSeven"""
from math import gcd
from fractions import Fraction as F
import random
def circ(x):
    f=x-(x.numerator//x.denominator); return min(f,1-f)
def clear_at(ds,e,k):
    return all(circ(F(d)*(F(8*k+1),8*e)[0]/1 if False else F(d)*F(8*k+1,8*e))>=F(1,8) for d in ds)
def A(ds): return len(set(ds))<=4
def B(ds): return len(set(ds))<=6
def C(ds):
    for e in set(ds):
        others=[d for d in ds if d!=e] or list(ds)
        lo=max(1,-(-e//min(others))); hi=(7*e)//max(others)
        q=lo+((1-lo)%8)
        if q<=hi and q>0 and all(F(1,8)<=F(d)*F(8*((q-1)//8)+1,8*e)<=F(7,8) for d in others):
            return True
    return False
def D(ds):
    for e in set(ds):
        rs=[F(d,e) for d in ds if d!=e]
        nonint=[r for r in rs if r.denominator!=1]
        ints=[r for r in rs if r.denominator==1]
        if len(nonint)<=1 and all(r.numerator%8!=0 for r in ints): return True
    return False
def E(ds):
    for e in set(ds):
        M=8*e
        if all(min((7*d)%M, M-(7*d)%M)>=e for d in ds if d!=e): return True
    return False
random.seed(5)
from collections import Counter
for hi,lab in ((20,'|v| <= 20'),(200,'|v| <= 200')):
    c=Counter(); tot=0
    for _ in range(20000):
        v=random.sample(range(-hi,hi+1),8); k=random.randrange(8)
        ds=[abs(v[i]-v[k]) for i in range(8) if i!=k]
        g=0
        for d in ds: g=gcd(g,d)
        ds=[d//g for d in ds]
        tot+=1
        hits=[n for n,f in (('A',A),('B',B),('C',C),('D',D),('E',E)) if f(ds)]
        c['covered' if hits else 'UNCOVERED']+=1
        for h in hits: c[h]+=1
    print(f"{lab}: subjects {tot}")
    print(f"   covered by the disjunction: {100*c['covered']/tot:6.2f}%    UNCOVERED {100*c['UNCOVERED']/tot:6.2f}%")
    print(f"   per condition: A {100*c['A']/tot:.2f}%  B {100*c['B']/tot:.2f}%  C {100*c['C']/tot:.2f}%  D {100*c['D']/tot:.2f}%  E {100*c['E']/tot:.2f}%")
