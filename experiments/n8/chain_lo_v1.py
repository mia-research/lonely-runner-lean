# E645: add the first window start lo_min (the first instant all six are 1/8-clear) and test it as a predictor of chain length, held out.
import csv, math
import numpy as np
from fractions import Fraction as F
from classes_lib_v1 import clear_iv, meet
def win(core):
    g = 0
    for d in core: g = math.gcd(g, d)
    T = F(1, g)
    J = clear_iv(F(core[0]), T)
    for s in core[1:]: J = meet(J, clear_iv(F(s), T))
    return [(lo, hi) for lo, hi in J if hi >= lo and lo > 0], T
if __name__ == '__main__':
    rows = []
    for r in csv.DictReader(open('chain_data_N12_v1.out'), delimiter='|'):
        core = tuple(map(int, r['core'].split(',')))
        J, T = win(core)
        rows.append(dict(core=core, chain=int(r['chain']), y0=float(F(r['y0'])), in53=r['in53'] == '1', lo=float(min(J)[0]), T=float(T), nw=len(J), runs=eval(r['runs'])))
    y = lambda rs: np.array([math.log(r['chain']) for r in rs])
    def X(rs, fe): return np.array([[1] + [f(r) for f in fe] for r in rs])
    sets = {'logy0': [lambda r: math.log(r['y0'])],
            'logy0+loglo': [lambda r: math.log(r['y0']), lambda r: math.log(r['lo'])],
            'log(y0*lo)': [lambda r: math.log(r['y0'] * r['lo'])],
            'log(y0*lo/T)': [lambda r: math.log(r['y0'] * r['lo'] / r['T'])]}
    train = [r for r in rows if not r['in53'] and max(r['core']) <= 10]
    test_out = [r for r in rows if not r['in53'] and max(r['core']) > 10]
    test53 = [r for r in rows if r['in53']]
    for nm, fe in sets.items():
        b, *_ = np.linalg.lstsq(X(train, fe), y(train), rcond=None)
        def ev(rs):
            e = np.exp(X(rs, fe) @ b) - np.array([r['chain'] for r in rs]); return round(float(np.sqrt((e ** 2).mean())), 2), round(float(np.abs(e).max()), 1)
        print(nm, 'coef', np.round(b, 2), 'train', ev(train), '| N11-12 out', ev(test_out), '| 53 cores', ev(test53))
    for r in sorted(test53, key=lambda r: -r['chain'])[:6]:
        print(r['core'], 'chain', r['chain'], 'y0', round(r['y0'], 1), 'lo_min', round(r['lo'], 3), 'T', round(r['T'], 3), 'nw', r['nw'])
    print('lo_min over all: min/median/max', min(r['lo'] for r in rows), np.median([r['lo'] for r in rows]), max(r['lo'] for r in rows))
    print('53 cores lo_min median', np.median([r['lo'] for r in test53]), ' others', np.median([r['lo'] for r in rows if not r['in53']]))

