# stress_seedcheck_v1.py -- claims G, C, S and class list on all 11,176 exact gate-crossing seeds; S slack per prefix length.
import sys, pickle; sys.path.insert(0, '.')
exec(open('stress_lib_v1.py').read())
from collections import Counter
seeds = pickle.load(open('stress_seeds_v1.pkl', 'rb')); cls = Counter(); viol = Counter(); pref = Counter(); slack = {}; mx = (0, None)
for r in seeds:
    rh = [Q(x) for x in r]; cl, R, v, o = check(rh); cls[cl] += 1
    for s in v: viol[s.split(':')[0].split('_step')[0]] += 1
    seen = set(); k = -1
    for i, s in enumerate(o['steps']):
        if s[1] in seen: break
        seen.add(s[1]); k = i
        if i <= 6:
            sl = rh[6 - i] / (7 * mpq(7, 9) ** i)
            if i not in slack or sl < slack[i][0]: slack[i] = (sl, r)
    pref[k + 1] += 1
    if Fr(R) > mx[0]: mx = (Fr(R), r)
print('seeds', len(seeds), 'classes', dict(cls), 'violations', dict(viol))
print('length of the distinct-setter prefix (count of seeds):', dict(sorted(pref.items())))
for i in sorted(slack): print('S slack k=%d : min rho_{7-k}/(7(7/9)^k) = %s (>1 required)' % (i, float(slack[i][0])))
print('max landing among seeds', mx[0], float(mx[0]))
