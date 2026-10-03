from ceil_lib_v1 import *
from ceil_k6_lib_v1 import *
x = norm(X7)
for name, sub in (('K6 (readings 1..6)', x[:6]), ('K7 (all)', x)):
    c = clear_components(sub, F(9)); print(name, 'components in [1,9]:', len(c))
    for a, b in c: print('   [%.9f, %.9f] len %.3e  in a reading-7 zone: %s' % (float(a), float(b), float(b-a), in_zone7(x[6], a, b)))
