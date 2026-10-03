# Float views of disc_records_v1.pkl for fast exploration (exact values stay in the pkl).
import pickle, numpy as np
recs = pickle.load(open('disc_records_v1.pkl','rb'))
n=len(recs)
rho=np.array([[float(x) for x in r[1]] for r in recs]); R=np.array([float(r[2]) for r in recs]); W=np.array([float(r[3]) for r in recs])
P=np.array([[float(x) for x in r[4]] for r in recs]); nm=np.array([len(r[6]) for r in recs])
setter=np.full((n,32),-1); lap=np.full((n,32),-1); S=np.full((n,34),np.nan)
for i,r in enumerate(recs):
    for k,(s,l) in enumerate(r[6]): setter[i,k]=s; lap[i,k]=l
    for k,s in enumerate(r[5]): S[i,k]=float(s)
cell=np.array([r[0] for r in recs])
np.savez('disc_floats_v1.npz',rho=rho,R=R,W=W,P=P,nm=nm,setter=setter,lap=lap,S=S,cell=cell)
print(n)
