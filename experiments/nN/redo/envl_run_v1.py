import sys; sys.path.insert(0,'.')
from envl_lp_v1 import *
J=int(sys.argv[1]); W={1:9,2:17}[J]; mode=sys.argv[2]   # full | pruned
SP='/private/tmp/claude-501/-Users-trentpalelei-Desktop-Math-Ex/ed62988a-aa4c-4682-b812-d4182b31b4a6/scratchpad/'
S=pickle.load(open(SP+f'envl_sigs_J{J}.pkl','rb')); T,M=load(J)
items=list(S.items())
out={}
t0=time.time()
if mode=='full':
    for k,(sg,(n,cnt,idx,rh)) in enumerate(items):
        A=rows(sg,W); lo=[];hi=[]
        for r in range(1,7):
            a=lp(A,r,1); b=lp(A,r,-1)
            lo.append(a.fun if a.status==0 else None); hi.append(-b.fun if b.status==0 else None)
        box=[(float(a),float(b)) for a,b in T[idx][3]]
        out[sg]=(n,idx,lo,hi,box)
        if k%1000==0: print(k,time.time()-t0,flush=True)
    pickle.dump(out,open(SP+f'envl_lpfull_J{J}.pkl','wb'))
