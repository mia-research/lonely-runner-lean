import random, time
from collections import Counter
exec(open('pred_lib_v1.py').read())
rnd = random.Random(1)
for name, f in FAMS:
    t = time.time(); c = Counter(); steps = 0
    for _ in range(300):
        xs = f(rnd); n = len(path(xs)[0]); c[n] += 1; steps += n
    print(name, sorted(c.items()), steps, "%.1fs" % (time.time() - t))
