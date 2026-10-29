# E643 control: search arithmetic-fitting sets built from (u,K,H,A,B) for one where the InWay part also holds, to show the full test can fire.
from fresh_class_test_v1 import *
found = 0
for K in (1, 2, 3, 4, 7):
  for u in (8 * K, 16 * K):
    for H in range(1, 4):
      for A in range(H, 7):
        for B in range(1, 7):
          if not (A <= 3 * B and B <= 3 * A): continue
          a, b, c = [F(u) * (8 * m + F(7, 8 * K)) for m in (H, A, B)]
          if any(x.denominator != 1 for x in (a, b, c)): continue
          a, b, c = int(a), int(b), int(c)
          e = (a + min(b, c)) // 2 if a < min(b, c) else a
          S = sorted({u, a, b, c, e, max(1, u // 4), max(1, u // 8) + 1})
          if len(S) != 7 or len(set(S)) != 7: continue
          r = test(S)
          if r['full']:
              found += 1
              if found <= 3: print('control fires', tuple(S), r['full'][0])
print('controls found', found)
