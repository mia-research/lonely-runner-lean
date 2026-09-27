import sys, adv
from multiprocessing import Pool
if __name__=="__main__":
    n=int(sys.argv[1]); base=int(sys.argv[2])
    with Pool(10) as p: res=p.map(adv.climb, range(base,base+n))
    bad=[r for r in res if isinstance(r[0],str)]
    res=[r for r in res if not isinstance(r[0],str)]
    res.sort(key=lambda r:r[0], reverse=True)
    print("restarts:",n," shapes with no clear R<=40:",len(bad))
    print("max least-clear R:",float(res[0][0]),"=",res[0][0]," shape:",[str(x) for x in res[0][1]])
    print("count least-clear >12:",sum(r[0]>12 for r in res))
    print("top 5:",[round(float(r[0]),6) for r in res[:5]])
    print("certificate witness failures on all final shapes:",adv.witness_all(res))
