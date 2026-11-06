# E822: the exact greedy chain (list of pieces) for the 970 sets of chain_data_N12_v1.out; pickle for the analysis scripts.
import csv, pickle
from multiprocessing import Pool
from gen_real_core_v1 import cert
from chain_fast_v1 import feats
def job(core):
    c = cert(core)
    return core, c['T'], c['y0'], c['chain']
if __name__ == '__main__':
    cores = [tuple(map(int, r['core'].split(','))) for r in csv.DictReader(open('chain_data_N12_v1.out'), delimiter='|')]
    with Pool(10) as p: res = p.map(job, cores, chunksize=4)
    pickle.dump(res, open('chain_pieces_v1.pkl', 'wb'))
    print('sets', len(res), 'pieces', sum(len(r[3]) for r in res))
