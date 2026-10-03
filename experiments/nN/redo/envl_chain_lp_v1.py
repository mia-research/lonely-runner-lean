# LP-level (whole sig region) check of the chain inequality rho_{7-k} > 7(7/9)^k for cascades with >= k+1 moves, split by whether the first k+1 setters are distinct
import sys,glob,pickle
from fractions import Fraction as F
SP='/private/tmp/claude-501/-Users-trentpalelei-Desktop-Math-Ex/ed62988a-aa4c-4682-b812-d4182b31b4a6/scratchpad/'
for J in (1,2):
    if J==1: o=pickle.load(open(SP+'envl_lpfull_J1.pkl','rb')); o={k:(v[0],v[1],v[2],v[3]) for k,v in o.items()}
    else:
        o={}
        for f in glob.glob(SP+'envl_chunk_J2_*.pkl'): o.update(pickle.load(open(f,'rb')))
    print('J',J,'sigs',len(o))
    for k in range(0,6):
        b=7*(7/9)**k; idx=6-k-1  # lo index: rank r -> r-2
        rk=7-k; li=rk-2
        dist=[v for sg,v in o.items() if v[0]>=k+1 and len({s for s,j,_ in sg[1:k+2]})==k+1]
        rep=[v for sg,v in o.items() if v[0]>=k+1 and len({s for s,j,_ in sg[1:k+2]})<k+1]
        def mn(L): return min(v[2][li] for v in L) if L else None
        vd=sum(1 for v in dist if v[2][li]<b-1e-9); vr=sum(1 for v in rep if v[2][li]<b-1e-9)
        print(f'  k={k} rank {rk} bound {b:.6f}: distinct-setter sigs {len(dist)} (violations {vd}, min {mn(dist)}), repeated-setter sigs {len(rep)} (violations {vr}, min {mn(rep)})')
