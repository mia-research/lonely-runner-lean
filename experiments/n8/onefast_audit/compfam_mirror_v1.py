# compfam_mirror_v1.py -- builds the bridge mirror: Fresh/JoinFamComposed.lean's composed-
# engine section (verbatim, pure Mathlib -- the sections ComposedFamData uses never touch
# FilterAssembly) + Fresh/ComposedFamData.lean's body with its import line swapped.
# Artifact only (compfam_bridge_mirror.lean); the REAL file is Fresh/ComposedFamData.lean,
# verified by ./check.sh.  Writes only under experiments/n8/onefast_audit/.
import os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
FRESH = os.path.join(HERE, '..', '..', '..', 'LonelyRunnerFresh', 'Fresh')


def build():
    src = open(os.path.join(FRESH, 'JoinFamComposed.lean')).read()
    i0 = src.index('namespace Fresh.JoinFamComposed')
    i1 = src.index('/-! ## 4.')
    engine = src[i0:i1]
    # drop the open (no FilterAssembly in the mirror)
    engine = engine.replace('open Fresh.FilterAssembly\n\n', '')
    # drop the two JoinEdge-dependent corollaries (not used by ComposedFamData)
    a = engine.index('/-- `Fresh.SpineSound.joinEdge_conflict` recovered')
    b = engine.index('/-! ## 2.')
    engine = engine[:a] + engine[b:]
    a = engine.index('/-- The raw `8m')
    b = engine.index('/-! ## 3.')
    engine = engine[:a] + engine[b:]
    header = 'import Mathlib\n\n/-!\n## BRIDGE MIRROR (artifact: experiments/n8/onefast_audit/compfam_bridge_mirror.lean)\n\nEngine: VERBATIM from Fresh/JoinFamComposed.lean (namespace Fresh.JoinFamComposed;\nthe composed-engine sections 1-3 use only Mathlib lemmas; the two JoinEdge-dependent\ncorollaries are dropped -- ComposedFamData does not use them).\nBody: VERBATIM from Fresh/ComposedFamData.lean with only the import line swapped\n(the bridge\'s `lake env lean` search path lacks LonelyRunnerFresh/build; the real file\nis ./check.sh-verified).  The #print axioms outputs apply verbatim to the real file.\n-/\n\n'
    body = open(os.path.join(FRESH, 'ComposedFamData.lean')).read()
    body = body.replace('import Fresh.JoinFamComposed\n', '', 1)
    return header + engine + 'end Fresh.JoinFamComposed\n\n' + body


if __name__ == '__main__':
    out = build()
    dst = os.path.join(HERE, 'compfam_bridge_mirror.lean')
    open(dst, 'w').write(out)
    print('wrote', dst, len(out), 'chars')
