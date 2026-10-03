import sys; sys.path.insert(0,'.')
from envl_lp_v1 import *
J=int(sys.argv[1]); i=int(sys.argv[2]); N=int(sys.argv[3]); W={1:9,2:17}[J]
SP='/private/tmp/claude-501/-Users-trentpalelei-Desktop-Math-Ex/ed62988a-aa4c-4682-b812-d4182b31b4a6/scratchpad/'
S=pickle.load(open(SP+f'envl_sigs_J{J}.pkl','rb')); items=list(S.items())[i::N]
out={}; t0=time.time()
for k,(sg,(n,cnt,idx,rh)) in enumerate(items):
    A=rows(sg,W); lo=[];hi=[]
    for r in range(1,7):
        a=lp(A,r,1); lo.append(a.fun if a.status==0 else None)
        if n>=10: b=lp(A,r,-1); hi.append(-b.fun if b.status==0 else None)
        else: hi.append(None)
    out[sg]=(n,idx,lo,hi)
    if time.time()-t0>540: print('TIMEOUT at',k,len(items)); break
pickle.dump(out,open(SP+f'envl_chunk_J{J}_{i}.pkl','wb')); print('done',i,len(out),time.time()-t0)
