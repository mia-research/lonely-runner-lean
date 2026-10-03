import glob,pickle,collections
SP='/private/tmp/claude-501/-Users-trentpalelei-Desktop-Math-Ex/ed62988a-aa4c-4682-b812-d4182b31b4a6/scratchpad/'
o1=pickle.load(open(SP+'envl_lpfull_J1.pkl','rb')); o1={k:(v[0],v[1],v[2],v[3]) for k,v in o1.items()}
o2={}
for f in glob.glob(SP+'envl_chunk_J2_*.pkl'): o2.update(pickle.load(open(f,'rb')))
for name,o in (('J1',o1),('J2',o2)):
    by=collections.defaultdict(list)
    for sg,(n,idx,lo,hi) in o.items():
        if n>=10: by[sg[1][1]].append(hi)   # lap of first setter
    for j in sorted(by):
        print(name,'first-setter lap',j,'sigs(>=10 moves)',len(by[j]),'max per rank 2..7 (closure LP):',[round(max(h[r] for h in by[j]),5) for r in range(6)])
    # also: min and max of lap of first move over all sigs
    print(name,'first-lap distribution all sigs',collections.Counter(sg[1][1] for sg in o))
