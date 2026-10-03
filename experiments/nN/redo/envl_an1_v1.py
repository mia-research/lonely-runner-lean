import sys; sys.path.insert(0,'.')
import pickle
SP='/private/tmp/claude-501/-Users-trentpalelei-Desktop-Math-Ex/ed62988a-aa4c-4682-b812-d4182b31b4a6/scratchpad/'
J=int(sys.argv[1]); o=pickle.load(open(SP+f'envl_lpfull_J{J}.pkl','rb'))
print('J',J,'sigs',len(o))
bad=0
for sg,(n,idx,lo,hi,box) in o.items():
    for r in range(6):
        if lo[r] is None or hi[r] is None: bad+=1;break
        if lo[r]<box[r+1][0]-1e-6 or hi[r]>box[r+1][1]+1e-6: bad+=1;break
print('sigs where LP range exceeds tree box or LP failed:',bad)
for th in (1,2,10):
    sel=[v for v in o.values() if v[0]>=th]
    print('nmoves>=',th,'cells',len(sel))
    print(' min',[round(min(v[2][r] for v in sel),5) for r in range(6)])
    print(' max',[round(max(v[3][r] for v in sel),5) for r in range(6)])
