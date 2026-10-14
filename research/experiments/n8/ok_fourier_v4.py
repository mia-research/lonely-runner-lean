r"""
ok_fourier_v4 -- (A): the SIGNED support-3 sum, and the general ray closed form.

For a primitive resonance p (support s) the ray sum is
    R(p) = sum_{m != 0} prod_j fhat(m p_j),  fhat(k) = -sin(pi k/4)/(pi k),
        = (-1)^s * 2 * sum_{m>=1} prod_j sin(pi m p_j /4) / (pi^s m^s prod_j p_j)   [s odd]
The product of s sines expands into sines/cosines of (+-p_1 +- ... +- p_s) * pi m/4, and
    sum_{m>=1} sin(m x)/m^3  and  sum_{m>=1} cos(m x)/m^2
are Bernoulli polynomials in x/pi with RATIONAL coefficients, times pi^3 resp. pi^2.  The
pi powers cancel against 1/pi^s, so EVERY ray sum is RATIONAL -- the Ray(p) rationality of
O_RESONANCE, now for |G| and at any support.  Checked numerically below.

Then: signed vs absolute support-3 and support-4 totals.  v2 showed the ABSOLUTE ones are
fatal (T3 ~ 0.275 against a main term of 0.133).  The question is what the signs leave.
"""
from itertools import combinations
from functools import reduce
from math import gcd, sin, pi
from fractions import Fraction as F

def fhat(k):
    if k==0: return 0.75
    if k%4==0: return 0.0
    return -sin(pi*k/4)/(pi*k)

def ray(p, M=60000):
    """signed sum over the ray {m p : m != 0}"""
    s=0.0
    for m in range(1,M+1):
        t=1.0
        for x in p:
            t*=fhat(m*x)
            if t==0.0: break
        s+=t
    return 2*s

print("ray sums R(p) for primitive support-3 vectors -- are they rational?")
for p in [(1,1,-1),(1,2,-1),(1,3,-2),(2,3,-1),(1,1,-2),(3,5,-2),(1,5,-3)]:
    v=ray(p)
    fr=F(v).limit_denominator(100000)
    print(f"  p = {str(p):12} R(p) = {v:14.10f}   ~ {str(fr):>14}"
          f"   err {abs(v-float(fr)):.2e}")

def sup_totals(E,size,H):
    """signed and absolute totals at support exactly `size`, |k| <= H"""
    sg=0.0; ab=0.0; w=0.75**(7-size)
    for idx in combinations(range(7),size):
        sub=[E[i] for i in idx]
        rng=range(-H,H+1)
        if size==3:
            a,b,c=sub
            for ka in rng:
                if ka==0 or ka%4==0: continue
                fa=fhat(ka)
                for kb in rng:
                    if kb==0 or kb%4==0: continue
                    r=-(ka*a+kb*b)
                    if r%c: continue
                    kc=r//c
                    if kc==0 or kc%4==0: continue
                    v=fa*fhat(kb)*fhat(kc)*w
                    sg+=v; ab+=abs(v)
        else:
            a,b,c,d=sub
            for ka in rng:
                if ka==0 or ka%4==0: continue
                for kb in rng:
                    if kb==0 or kb%4==0: continue
                    for kc in rng:
                        if kc==0 or kc%4==0: continue
                        r=-(ka*a+kb*b+kc*c)
                        if r%d: continue
                        kd=r//d
                        if kd==0 or kd%4==0: continue
                        v=fhat(ka)*fhat(kb)*fhat(kc)*fhat(kd)*w
                        sg+=v; ab+=abs(v)
    return sg,ab

print(f"\nsigned vs absolute, supports 3 and 4      (main term (3/4)^7 = {0.75**7:.6f})")
print(f"{'E':28} {'sgn S3':>10} {'abs S3':>10} {'sgn S4':>10} {'abs S4':>10} {'|sgn|/abs S3':>13}")
for E in [(2,6,7,8,10,13,14),(1,3,4,5,7,11,24),(1,3,5,7,13,15,24),(3,10,14,15,16,19,21)]:
    s3,a3=sup_totals(list(E),3,30); s4,a4=sup_totals(list(E),4,12)
    print(f"{str(E):28} {s3:10.6f} {a3:10.6f} {s4:10.6f} {a4:10.6f} {abs(s3)/a3:13.4f}")
