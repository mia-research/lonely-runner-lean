# Uniform original endpoint bounds for three blocks

Rules: 1–4, 8–18. Root internal-phase theorem and catalogue remain untouched.

- [L] New `Fresh/ThreeBlockEndpointBounds.lean` treats every p,q≥1,p+q≤7, positive originalg,h withg+h≤2, by three symbolic block cases. There is no enumeration of partitions or labels.
- [L] `left_difference_bounds` derives every original positive left-end disparity in[1,7], using only the guard `p=1→g≥1`. For subject labeli, the three expressions arei, `g+i−1`, `g+h+i−2`.
- [L] `right_difference_bounds` derives every original positive right-end disparity in[1,7], using only `p+q=7→h≥1`. The expressions are `g+h+5−i`, `h+6−i`, `7−i`.
- [L] `left_direct` and `right_direct` prove `IsolatedAt (ThreeBlockPartitions.speeds c g h p q) 0/7 (1/8)` from those original-reading bands. Right signed readings use exact reflection; all seven readings and equality edges remain present.
- [OBS] The guards handle precisely the adjacent endpoint-singleton lower-bound obligations. The previously saved guard-free singleton failures are not asserted to satisfy these hypotheses.
- [SOURCE] The targets consume the established physical block speed function and qualified saved singleton controls. They do not assume a future isolation, candidate-clear predicate, floating point result or move bound.
- [L] All four endpoints compile with exactly `[propext, Classical.choice, Quot.sound]`; source scans find zero sorry/native_decide/axiom/admit/unsafe declarations. The exact positional argument order is `(c g h)(p q) hp hq hpq hg hh hsmall hguard`, followed by label/distinctness for the two difference helpers.
- [OWED] Root combines these endpoint targets with the independent lifted-neighbour input theorem for the all21-partition consumer. No arbitrary independent-gap lap witness or full n=8 theorem is claimed here.
