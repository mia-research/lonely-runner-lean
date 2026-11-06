# E827: the least-uncovered readings of each double-carve annealing seed (frontier_double_carve_v1_s*.out) pushed through the exact cascade of LonelyRunner/experiments/nN/redo/outcome_classes_v2.py (Fractions of the float readings).
import re, glob, os
from fractions import Fraction as F
HERE = os.getcwd(); os.chdir('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/')
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
os.chdir(HERE)
for f in sorted(glob.glob('frontier_double_carve_v1_s*.out')):
    l = open(f).readline()
    m = re.search(r'readings \[(.*)\]', l)
    v = [float(x) for x in m.group(1).split(',')]
    rh = [F(1)] + [F(x) for x in v]
    o = outcome(rh)
    print(f[-6:-4], 'least-uncovered readings, rho7 =', float(rh[-1]), '| cascade landing R =', float(o['R']), '| window', int((o['R'] - 1) // 8), '| moves', o['nmoves'], '| landing below 17:', o['R'] < 17, '| exact R =', o['R'])
