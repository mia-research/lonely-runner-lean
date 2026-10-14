"""The two-walker case.  At flank e, opening k, ratio rho with fractional part f sits at
   k*f + rho/8   (mod 1),  and is CLEAR iff its distance to Z is >= 1/8.
The flank itself is free.  Integer ratios are stationary.  So the open case is the WALKERS.

RUN-LENGTH IDEA: a walker with effective step  ghat = min(f, 1-f)  stays in the bad arc (length
1/4) for at most (1/4)/ghat + 1 consecutive k, and stays clear (arc 3/4) for at least
(3/4)/ghat - 1.  If the SLOWER walker's clear run outlasts the FASTER walker's bad run, some k
has both clear -- no counting, no density.  Where does that bite, and what survives it?
Exact Fraction."""
import random
from fractions import Fraction as F
from math import floor, gcd

TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def clear(f,c,k): return circd(F(k)*f+c)>=TH
def min_k_two(f1,c1,f2,c2,KMAX=4000):
    for k in range(KMAX+1):
        if clear(f1,c1,k) and clear(f2,c2,k): return k
    return None
def ghat(f): return min(f,1-f)
def runlen_ok(f1,f2):
    g1,g2=sorted([ghat(f1),ghat(f2)])
    if g1==0 or g2==0: return None
    return (F(3,4)/g1 - 1) > (F(1,4)/g2 + 1)

print("=== 1. is the two-walker case even TRUE?  adversarial over rational f ===")
bad=[]
for q1 in range(2,15):
    for q2 in range(2,15):
        for p1 in range(1,q1):
            if gcd(p1,q1)!=1: continue
            for p2 in range(1,q2):
                if gcd(p2,q2)!=1: continue
                f1,f2=F(p1,q1),F(p2,q2)
                for A1 in range(0,8):
                    for A2 in range(0,8):
                        c1=(F(A1)+f1)/8; c2=(F(A2)+f2)/8
                        if min_k_two(f1,c1,f2,c2,200) is None:
                            bad.append((f1,A1,f2,A2))
print(f"   shadowing pairs found (no clear k <= 200): {len(bad)}")
if bad:
    fs=sorted({(str(a),str(c)) for a,_,c,_ in bad})
    print(f"   distinct fractional-part pairs among them: {fs[:10]}{' ...' if len(fs)>10 else ''}")
    print(f"   example: rho1 = {bad[0][1]} + {bad[0][0]},  rho2 = {bad[0][3]} + {bad[0][2]}")
    print(f"   whole-part classes (A1,A2) seen: {sorted({(a,b) for _,a,_,b in bad})}")

print()
print("=== 2. does the run-length criterion decide the cases it claims? ===")
rng=random.Random(4); ok=0; tot=0; viol=0; maxk_ok=0; maxk_no=0
for _ in range(20000):
    f1=F(rng.randint(1,999),1000); f2=F(rng.randint(1,999),1000)
    A1=rng.randrange(8); A2=rng.randrange(8)
    c1=(F(A1)+f1)/8; c2=(F(A2)+f2)/8
    r=runlen_ok(f1,f2); k=min_k_two(f1,c1,f2,c2,3000)
    tot+=1
    if r:
        ok+=1
        if k is None: viol+=1
        else: maxk_ok=max(maxk_ok,k)
    else:
        if k is not None: maxk_no=max(maxk_no,k)
print(f"   criterion fires on {ok}/{tot} = {ok/tot:.4f} of sampled pairs")
print(f"   VIOLATIONS (fired but no clear k): {viol}     max k where it fired: {maxk_ok}")
print(f"   max k among cases where it did NOT fire: {maxk_no}")
print()
print("   the criterion needs the faster walker's ghat below:")
for g2 in [F(1,2),F(1,3),F(1,4),F(1,5),F(1,8)]:
    g1=g2
    print(f"      ghat1 = ghat2 = {g2}:  (3/4)/g1 - 1 = {float(F(3,4)/g1-1):.3f}  vs  (1/4)/g2 + 1 = {float(F(1,4)/g2+1):.3f}  -> {'FIRES' if (F(3,4)/g1-1)>(F(1,4)/g2+1) else 'silent'}")

print()
print("=== 3. the SIMPLIFIED criterion:  ghat2 = max(ghat) < 1/4  =>  clear opening exists ===")
rng=random.Random(99); fired=0; viol=0; tot=0; mk=0
worst=None
for _ in range(40000):
    f1=F(rng.randint(1,9999),10000); f2=F(rng.randint(1,9999),10000)
    A1=rng.randrange(8); A2=rng.randrange(8)
    c1=(F(A1)+f1)/8; c2=(F(A2)+f2)/8
    g=max(ghat(f1),ghat(f2)); tot+=1
    if g<F(1,4):
        fired+=1
        k=min_k_two(f1,c1,f2,c2,6000)
        if k is None: viol+=1
        else:
            if k>mk: mk=k; worst=(f1,A1,f2,A2)
print(f"   fires on {fired}/{tot} = {fired/tot:.4f}")
print(f"   VIOLATIONS: {viol}")
print(f"   largest k needed when it fires: {mk}   at f1={worst[0]} A1={worst[1]} f2={worst[2]} A2={worst[3]}")
print(f"   predicted index bound (1/ghat_min): {float(1/min(ghat(worst[0]),ghat(worst[2]))):.1f}")
print()
print("=== 4. what survives?  cases with max ghat >= 1/4 ===")
rng=random.Random(5); surv=0; noclear=0; ks=[]
for _ in range(40000):
    f1=F(rng.randint(1,9999),10000); f2=F(rng.randint(1,9999),10000)
    A1=rng.randrange(8); A2=rng.randrange(8)
    c1=(F(A1)+f1)/8; c2=(F(A2)+f2)/8
    if max(ghat(f1),ghat(f2))<F(1,4): continue
    surv+=1
    k=min_k_two(f1,c1,f2,c2,4000)
    if k is None: noclear+=1
    else: ks.append(k)
import statistics as st
print(f"   residue size: {surv}/40000 = {surv/40000:.4f}")
print(f"   of those, NO clear k <= 4000: {noclear}")
print(f"   min k needed: mean {st.mean(ks):.2f}  max {max(ks)}")
