# 2026-10-29: write BS-free parallel copies (suffix Free) of the modules in my chain that reach the Barajas-Serra route.  Originals untouched.
import re, os, sys
os.chdir('Fresh')
T = ['Nv_RealSevenN','Nv_BlockSplitEightN','Nv_OneFreeEightN','Nv_OrderEightCasesN','Nv_ParityCoverN','Nv_ParityDescentN','Nv_ParityDescentTwoN','Nv_ParityMixedOneThreeN','Nv_ParityMixedTwoTwoN','Nv_RealEightN','Nv_ResidueCasesN','Nv_ResidueCasesTwoN',
     'ClusterWindow','CoreCover','CoreFamilies','CoreFamiliesGenA','CoreFamiliesGenB','CoreFamiliesGenC','CoreFamiliesGenD','EightResidualNative','EightResidualOpen','FlankBand','NativeClusters','NativeOrders','RealFromNat','ResidualDischarge','ResidualRest4']
TS = set(T)
for m in T:
    s = open(m + '.lean').read()
    if m == 'Nv_RealSevenN':
        s = '''-- BS-free 2026-10-29: order seven real speeds from the native certificate proof.  Keeps the namespace of the original so dependent copies need no renaming.
import Fresh.Nv_OrderSevenNativeN
import Fresh.Nv_RealSixN

namespace LRC.OrderSevenN

open LRC.SpecN

theorem existenceAtN_seven : ExistenceAtN 7 := LRC.OrderSevenNative.existenceAtN_seven

theorem lonelyRunnerAtN_seven : LonelyRunnerAtN 7 := LRC.OrderSevenNative.lonelyRunnerAtN_seven

end LRC.OrderSevenN
'''
        open(m + 'Free.lean', 'w').write(s); continue
    s = re.sub(r'^import Fresh\.(\S+)', lambda mo: 'import Fresh.' + mo.group(1) + ('Free' if mo.group(1) in TS else ''), s, flags=re.M)
    s = s.replace('LRC.OrderSevenN.lonely_seven_nat', 'LRC.OrderSevenNative.lonely_seven_nat')
    s = s.replace('LRC.OrderSevenN.quotient_card_sum', 'Fresh.FreeHelpers.quotient_card_sum')
    s = s.replace('Fresh.NativeOrders.', 'Fresh.NativeOrdersFree.').replace('Fresh.RealFromNat.', 'Fresh.RealFromNatFree.')
    s = s.replace('namespace Fresh.NativeOrders\n', 'namespace Fresh.NativeOrdersFree\n').replace('end Fresh.NativeOrders\n', 'end Fresh.NativeOrdersFree\n')
    s = s.replace('namespace Fresh.RealFromNat\n', 'namespace Fresh.RealFromNatFree\n').replace('end Fresh.RealFromNat\n', 'end Fresh.RealFromNatFree\n')
    s = re.sub(r'open ([^\n]*)Fresh\.NativeOrders\b(?!Free)', lambda mo: 'open ' + mo.group(1) + 'Fresh.NativeOrdersFree', s)
    s = re.sub(r'open ([^\n]*)Fresh\.RealFromNat\b(?!Free)', lambda mo: 'open ' + mo.group(1) + 'Fresh.RealFromNatFree', s)
    if 'FreeHelpers' in s:
        s = s.replace('import Mathlib', 'import Mathlib\nimport Fresh.FreeHelpers', 1)
    if 'OrderSevenNative' in s and 'import Fresh.Nv_OrderSevenNativeN' not in s:
        s = s.replace('import Mathlib', 'import Mathlib\nimport Fresh.Nv_OrderSevenNativeN', 1) if 'import Mathlib' in s else 'import Fresh.Nv_OrderSevenNativeN\n' + s
    open((m + 'Free.lean') if m not in ('NativeOrders', 'RealFromNat') else m + 'Free.lean.new', 'w').write(s)
print('done')
