# E828: the least-uncovered arrangement each band search reached (laps 4 to 9 of r7), pushed through the exact cascade of outcome_classes_v2.py: if [1,7] is not carved the cascade lands in W_0 (R < 7); a landing above 7 means a carve.
import glob, pickle, os, re
from fractions import Fraction as F
HERE = os.getcwd(); os.chdir('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/')
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
os.chdir(HERE)
for f in sorted(glob.glob('frontier_band_best_v1_k*_s*.pkl')):
    best, x = pickle.load(open(f, 'rb'))
    if x is None: continue
    o = outcome([F(1)] + [F(v) for v in x])
    print(re.search(r'k(\d+)_s(\d+)', f).group(0), 'r7 =', float(x[5]), '| cascade landing R =', float(o['R']), '| window', int((o['R'] - 1) // 8), '| moves', o['nmoves'], '| landing past 7 (a carve):', o['R'] > 7, '| exact R =', o['R'])
