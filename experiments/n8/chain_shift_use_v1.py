# E645: for each of the 53 cores, the shifts d and windows used by the certificate chain (gen_real_core_v1.cert).
from multiprocessing import Pool
from gen_real_core_v1 import cert
def job(core):
    c = cert(core); ch = c['chain']
    return core, len(ch), sorted(set(int(d / c['T']) for a, b, lo, hi, d, k in ch)), len(set((lo, hi) for a, b, lo, hi, d, k in ch)), sum(1 for a, b, lo, hi, d, k in ch if d != 0)
if __name__ == '__main__':
    cores = [tuple(int(x) for x in l.split(',')) for l in open('core_cover_cores.txt') if l.strip()]
    with Pool(10) as p: res = p.map(job, cores)
    for r in res: print(r)
    print('cores', len(res), 'pieces', sum(r[1] for r in res), 'pieces with d != 0:', sum(r[4] for r in res), 'cores using any d != 0:', sum(1 for r in res if r[4]))
