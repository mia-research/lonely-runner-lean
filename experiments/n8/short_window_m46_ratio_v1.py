import pickle
from fractions import Fraction as Fr
rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl','rb'))
rs = sorted(Fr(x) for x in rec[46][1])
print([float(x) for x in rs])
r3, r6 = rs[2], rs[5]
d = r6/r3 - Fr(23,17)
print('rho6/rho3 - 23/17 =', d, float(d), abs(d) < Fr(1,10**13), abs(d) < Fr(1,10**12))
a, b = Fr(17,8)/r3, Fr(23,8)/r6
print('window', b-a, float(b-a))
