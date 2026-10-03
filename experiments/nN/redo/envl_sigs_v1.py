import sys; sys.path.insert(0,'.')
from envl_common_v1 import *
J=int(sys.argv[1]); T,M=load(J)
S={}
for idx,rh in M:
    sg,n=signature(rh)
    d=S.setdefault(sg,[n,0,idx,rh]); d[1]+=1
pickle.dump(S,open(f'/private/tmp/claude-501/-Users-trentpalelei-Desktop-Math-Ex/ed62988a-aa4c-4682-b812-d4182b31b4a6/scratchpad/envl_sigs_J{J}.pkl','wb'))
print('J',J,'members',len(M),'signatures',len(S),'with >=2 moves',sum(1 for v in S.values() if v[0]>=2),'>=10',sum(1 for v in S.values() if v[0]>=10))
