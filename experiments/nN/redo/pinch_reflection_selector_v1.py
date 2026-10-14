"""Exact, speed-dependent replacement labels at rational pinches.

The old event is supplied. No cascade is used to choose its replacement.
Choose N=lcm denominators(8*d_i*t), lambda=8*N-1, and
q'_i = 8*N*d_i*t - q_i - 1. These are natural labels and reflect the
old clear readings exactly. Verify an actual right parameter neighbourhood,
not just clearance at the pinched parameter.
This is local transport, not a finite-cover or universal n=8 theorem.
"""
from fractions import Fraction as F
from math import floor, lcm
from collections import Counter
import random
from window_transport_comparison_v1 import interval, path


def select(a,b,q,tau):
    ds=[d+tau*v for d,v in zip(a,b)]
    t=max(F(8*k+1,8)/d for k,d in zip(q,ds))
    assert t == min(F(8*k+7,8)/d for k,d in zip(q,ds))
    N=lcm(*[(8*d*t).denominator for d in ds])
    lam=8*N-1
    periods=[8*N*d*t for d in ds]
    assert all(p.denominator == 1 for p in periods)
    replacement=tuple(int(p)-k-1 for p,k in zip(periods,q))
    assert all(k>=0 for k in replacement)
    assert replacement == tuple(floor(d*lam*t) for d in ds)
    return replacement,lam,t


def check(a,b,q,tau):
    old=interval(a,b,q)
    assert old is not None and old[0] < tau == old[1] < 1
    p,lam,t=select(a,b,q,tau)
    new=interval(a,b,p)
    assert new is not None and new[0] <= tau < new[1], (q,p,tau,new)
    active=0
    for i in range(7):
        for j in range(7):
            A=(8*q[j]+7)*a[i]-(8*q[i]+1)*a[j]
            B=(8*q[j]+7)*b[i]-(8*q[i]+1)*b[j]
            C=(8*p[i]+7)*a[j]-(8*p[j]+1)*a[i]
            D=(8*p[i]+7)*b[j]-(8*p[j]+1)*b[i]
            assert C+tau*D == A+tau*B
            if A+tau*B == 0:
                active+=1
                assert B <= 0 and D == -lam*B and D >= 0
    return active,lam,new[1]-tau


def run():
    rng=random.Random(179)
    targets=[(0,1,50,105,106,136,189,199), (0,99,200,300,400,500,600,700)]
    targets += [(0,)+tuple(sorted(rng.sample(range(1,201),7))) for _ in range(12)]
    summary=Counter(); maxlam=0; least=None
    for target in targets:
        xs=[F(7)*(x-target[0])/(target[-1]-target[0]) for x in target]
        for subject in range(8):
            _,windows,_=path(target,subject)
            ids=[j for j in range(8) if j!=subject]
            a=[F(abs(j-subject)) for j in ids]
            b=[abs(xs[j]-xs[subject])-v for j,v in zip(ids,a)]
            for q,(lo,hi) in windows.items():
                if lo < hi < 1:
                    active,lam,width=check(a,b,q,hi)
                    summary['AP_path_pinches']+=1
                    summary['multiple_active']+=active>1
                    maxlam=max(maxlam,lam)
                    least=width if least is None else min(least,width)
    # Deliberate simultaneous boundaries: all seven readings can be on edges.
    for trial in range(100):
        edge=[1,7]+[rng.choice((1,3,4,5,7)) for _ in range(5)]
        q=tuple(rng.randrange(6) for _ in range(7))
        ds=[F(8*k+c,8) for k,c in zip(q,edge)]
        b=[-d if c==1 else d if c==7 else F(rng.randrange(-5,6),10)
           for d,c in zip(ds,edge)]
        # Pinch at s=1/2; scale derivatives to preserve positive speeds on [0,1].
        b=[v/10 for v in b]
        a=[d-v/2 for d,v in zip(ds,b)]
        active,lam,width=check(a,b,q,F(1,2))
        summary['constructed_simultaneous_pinches']+=1
        assert active>=1
    print(dict(summary))
    print('largest selected multiplier',maxlam)
    print('smallest right interval in AP tests',least)
    print('All selected labels were computed by the period formula, not the cascade.')
    # A deliberate global-progress diagnostic. Local continuation is NOT a
    # guarantee that iterating this selector covers the full deformation path.
    target=(1,50,105,106,136,189,199)
    a=list(map(F,range(1,8)))
    b=[F(7*x,199)-u for x,u in zip(target,a)]
    q=tuple(floor(F(3,8)*u) for u in a)
    for move in range(32):
        lo,hi=interval(a,b,q)
        if move in (0,1,2,4,8,16,31):
            print('REPEATED_REFLECTION',move,'right_approx',float(hi),
                  'maximum_lap_digits',len(str(max(q))))
        if hi == 1:
            print('REPEATED_REFLECTION reached endpoint')
            break
        q,lam,t=select(a,b,q,hi)
    else:
        print('REPEATED_REFLECTION did not reach endpoint in 32 steps;')
        print('this is a finite diagnostic, not a proof of infinite accumulation.')


if __name__=='__main__':
    run()
