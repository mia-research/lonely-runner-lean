"""Which (m,j,c) options cover the integer Case B sets; greedy cover."""
import pickle, time
from collections import Counter
from multiprocessing import Pool
from core import integer_caseB, class_works, CLASSES

def work(A):
    ws=[]
    for m in range(1,5):
        for j in range(7):
            for c in CLASSES:
                if class_works(A,j,m,c) is not None: ws.append((m,j,c))
    return A, ws

if __name__=='__main__':
    sets=list(integer_caseB(24))
    res={}
    with Pool(9) as p:
        for A,ws in p.imap_unordered(work,sets,chunksize=500): res[A]=ws
    pickle.dump(res,open('optstats_v1.pkl','wb'))
    cnt=Counter(o for ws in res.values() for o in ws)
    print('coverage per option (top 40):')
    for o,v in cnt.most_common(40): print(' ',o,v)
    # greedy cover
    un=set(res); chosen=[]
    while un:
        c2=Counter(o for A in un for o in res[A])
        o,v=c2.most_common(1)[0]; chosen.append((o,v))
        un={A for A in un if o not in res[A]}
    print('greedy cover size',len(chosen))
    for o,v in chosen: print(' ',o,v)
