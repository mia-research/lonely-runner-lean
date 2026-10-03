import pickle, os
def load_known():
    f='lat_known_paths_v1.pkl'
    if os.path.exists(f): return pickle.load(open(f,'rb'))
    K={}
    for tag,fn in (('J1','terminals7_J1.pkl'),('J2','terminals7_J2.pkl')):
        d=pickle.load(open(fn,'rb')); K[tag]=set(tuple(x[0]) for x in d)
    pickle.dump(K,open(f,'wb')); return K
