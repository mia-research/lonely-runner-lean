"""Select replacement labels from old readings, before testing clearance.

Double the old pinch time and backtrack to the latest preceding opening.
Carry bit: q'_i=2*q_i+1 iff old fractional reading >=9/16; else 2*q_i.
Only old phases in (7/16,9/16) can obstruct. Their backward repair needs
must fit inside the minimum age since the last opening of every reading.
Exact rational checks; no global coverage or termination claim.
"""
from fractions import Fraction as F
from math import floor
from collections import Counter
import random
from window_transport_comparison_v1 import interval,path,clear


def candidate(ds,q,t):
    f=[d*t-k for d,k in zip(ds,q)]
    assert all(F(1,8)<=x<=F(7,8) for x in f)
    bits=[int(x>=F(9,16)) for x in f]
    new=tuple(2*k+c for k,c in zip(q,bits))
    assert new==tuple(floor(2*d*t-F(1,8)) for d in ds)
    ages=[(2*x-c-F(1,8))/d for x,c,d in zip(f,bits,ds)]
    back=min(ages)
    need=max([F(0)]+[(2*x-F(7,8))/d for x,d in zip(f,ds)
                     if F(7,16)<x<F(9,16)])
    T=2*t-back
    assert T==max(F(8*k+1,8)/d for k,d in zip(new,ds))
    verdict=all(clear(d,T) for d in ds)
    assert verdict==(need<=back)
    return new,T,back,need,f


def run():
    rng=random.Random(179)
    targets=[(0,1,50,105,106,136,189,199),(0,99,200,300,400,500,600,700)]
    targets += [(0,)+tuple(sorted(rng.sample(range(1,201),7))) for _ in range(12)]
    counts=Counter(); failure=None
    for target in targets:
        xs=[F(7)*(x-target[0])/(target[-1]-target[0]) for x in target]
        for subject in range(8):
            _,windows,_=path(target,subject)
            ids=[j for j in range(8) if j!=subject]
            a=[F(abs(j-subject)) for j in ids]
            b=[abs(xs[j]-xs[subject])-v for j,v in zip(ids,a)]
            for q,(lo,tau) in windows.items():
                if not lo<tau<1: continue
                ds=[d+tau*v for d,v in zip(a,b)]
                t=max(F(8*k+1,8)/d for k,d in zip(q,ds))
                p,T,back,need,f=candidate(ds,q,t)
                w=interval(a,b,p)
                counts['pinches']+=1
                if need>back:
                    counts['fails_clearance']+=1
                    if failure is None:
                        failure=(target,subject,q,str(tau),p,str(back),str(need))
                elif w is not None and w[0]<=tau<w[1]:
                    counts['extends_right']+=1
                else:
                    counts['clear_but_no_right_extension']+=1
    print('RESULTS',dict(counts))
    print('FIRST_FAILURE',failure)
    # The planned comparison: labels are obtained from the rule, not provided.
    target=(1,50,105,106,136,189,199)
    a=list(map(F,range(1,8))); b=[F(7*x,199)-u for x,u in zip(target,a)]
    old=(0,0,1,1,1,2,2); tau=interval(a,b,old)[1]
    ds=[d+tau*v for d,v in zip(a,b)]
    t=max(F(8*k+1,8)/d for k,d in zip(old,ds))
    p,T,back,need,f=candidate(ds,old,t)
    print('WIDE old pinch',tau,'old time',t)
    print('WIDE old phases',tuple(map(str,f)))
    print('WIDE selected labels',p,'time',T)
    print('WIDE backward allowance',back,'required',need,'strict margin',back-need)
    print('WIDE exact parameter interval',tuple(map(str,interval(a,b,p))))
    assert p==(0,1,2,2,3,4,5)
    assert T==F(41,56)
    # Equality cannot be promoted to right extension without checking slopes.
    ds=list(map(F,(F(1,8),F(7,8),F(9,16),F(7,16),F(1,4),F(3,8),F(5,8))))
    b=[-ds[0]/10,ds[1]/10,-ds[2]/10,ds[3]/10,F(0),F(0),F(0)]
    tau=F(1,2); a=[d-tau*v for d,v in zip(ds,b)]; q=(0,)*7
    p,T,back,need,_=candidate(ds,q,F(1))
    old_window=interval(a,b,q); new_window=interval(a,b,p)
    assert old_window[0]<tau==old_window[1]
    assert back==need==0 and all(clear(d,T) for d in ds)
    assert new_window[1]==tau
    print('BOUNDARY_REGRESSION clear at pinch but no right extension:',p)


if __name__=='__main__':
    run()
