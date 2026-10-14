"""
Structure of a tight instance's witness -- proved statements, checked mechanically.

T = n-1 distinct positive integers, gcd 1, M(T) = 1/n exactly (TIGHT).
t* a witness (min_v ||v t*|| = 1/n).  All arithmetic exact.

PROVED (each check below re-derives the statement on every enumerated instance):

 (i)  There are a, b in T with  frac(a t*) = 1/n  and  frac(b t*) = (n-1)/n.
      [Else g(t) = min_v ||v t|| has all active slopes of one sign at t*, so g
       exceeds 1/n just to one side -- contradicting M(T) = 1/n.]

 (ii) a t* = 1/n and b t* = -1/n mod 1 give (a+b) t* in Z, so t* = p/q in lowest
      terms with  q | a+b.  In particular q <= a + b <= 2 max(T).

 (iii) a p / q - 1/n in Z gives q | n a p, and gcd(p,q)=1 gives q | n a; reducing
      mod n gives  n | q.  Write q = n r.  Then r | a and r | b, and with
      a = r a1, b = r b1:   a1 p = 1 (mod n),  b1 p = -1 (mod n).

 (iv) SUPPOSE n | d for some d in T, d = n d1.  Then
         d p mod n r = n * (d1 p mod r),
      so ||d t*|| = (n/(n r)) * min(s, r-s) with s = d1 p mod r.  If r = 1 then
      s = 0 and ||d t*|| = 0 < 1/n -- contradiction.  Hence  r >= 2,  i.e.  q >= 2n,
      and moreover r does not divide d1.

 CONSEQUENCE.  "no tight instance contains a multiple of n"  <=>  "every tight
 instance has witness denominator exactly n (r = 1)".  The two are equivalent, and
 the second is a purely arithmetic statement about one rational.
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd
import sys

def fn(x):
    r=x-(x.numerator//x.denominator); return r if r<=F(1,2) else 1-r

def covered(T,n):
    iv=[]
    for v in T:
        w=F(1,n*v)
        for k in range(0,v+1):
            lo,hi=F(k,v)-w,F(k,v)+w
            if hi<=0 or lo>=1: continue
            iv.append((max(lo,F(0)),min(hi,F(1))))
    iv.sort(); cur=F(0)
    for lo,hi in iv:
        if lo>cur: return False
        if hi>cur: cur=hi
    return cur>=1

def witnesses(T,n):
    dens=set(2*v for v in T)
    for a,b in combinations(T,2): dens.add(a+b); dens.add(abs(a-b))
    dens.discard(0); W=set()
    for d in dens:
        for k in range(1,d):
            t=F(k,d)
            if min(fn(v*t) for v in T)==F(1,n): W.add(t)
    return sorted(W)

def maximal_levels(n):
    qs=list(range(2,n))
    return [q for q in qs if not any(q2%q==0 and q2!=q for q2 in qs)]

def check(T,n):
    """Verify (i)-(iv) on one tight instance; return the list of r values seen."""
    rs=[]
    for t in witnesses(T,n):
        A=[v for v in T if (v*t)-((v*t).numerator//(v*t).denominator)==F(1,n)]
        B=[v for v in T if (v*t)-((v*t).numerator//(v*t).denominator)==F(n-1,n)]
        assert A and B, f"(i) FAILS on {T} at {t}"
        q=t.denominator
        assert any((a+b)%q==0 for a in A for b in B), f"(ii) FAILS on {T} at {t}"
        assert q%n==0, f"(iii) n|q FAILS on {T} at {t}"
        r=q//n
        for a in A+B: assert a%r==0, f"(iii) r|a FAILS on {T} at {t}"
        if any(v%n==0 for v in T): assert r>=2, f"(iv) FAILS on {T} at {t}"
        rs.append(r)
    return rs

def run(n,V):
    lv=maximal_levels(n); tight=[]; rvals=set(); withmult=0
    for T in combinations(range(1,V+1),n-1):
        if lv and not all(any(v%q==0 for v in T) for q in lv): continue
        g=0
        for v in T: g=gcd(g,v)
        if g!=1: continue
        if covered(T,n):
            tight.append(T)
            rvals.update(check(T,n))
            if any(v%n==0 for v in T): withmult+=1
    print(f"n={n} V<={V}: {len(tight)} tight; witness r values seen = {sorted(rvals)}; "
          f"containing a multiple of n: {withmult}")
    for T in tight: print(f"     {T}")
    return tight

if __name__=="__main__":
    for n,V in ((5,70),(6,50),(7,34)):
        run(n,V)
