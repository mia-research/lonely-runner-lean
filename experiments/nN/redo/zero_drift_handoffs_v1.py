"""Force observed pair-return drifts to zero, then follow all seven readings.

Consumes the exact handoff-boundary experiment. A target return with lap
advances (r,s) suggests the resonance v_b/v_a=s/r. Move v_b exactly there,
retaining all other speeds. This is a targeted perturbation, not a census.
"""
from fractions import Fraction as F
from collections import Counter
import argparse
import json
import unittest
from handoff_boundaries_v1 import trace, recurrence_records, compact_trace, frac, partition, distance, H


def event_times(v,lo,hi):
    times={lo,hi}
    for d in v:
        for k in range((d*lo).__floor__()-1,(d*hi).__floor__()+2):
            for sign in (-1,1):
                t=(F(k)+sign*H)/d
                if lo <= t <= hi:
                    times.add(t)
    return sorted(times)


def clear_pair_windows(v,pair,lo,hi):
    ds=[v[i] for i in pair]
    times=event_times(ds,lo,hi)
    pieces=[]
    for t in times:
        if all(distance(d*t)>=H for d in ds):
            pieces.append((t,t))
    for l,r in zip(times,times[1:]):
        if all(distance(d*(l+r)/2)>=H for d in ds):
            pieces.append((l,r))
    pieces.sort()
    merged=[]
    for l,r in pieces:
        if merged and l<=merged[-1][1]:
            merged[-1]=(merged[-1][0],max(r,merged[-1][1]))
        else:
            merged.append((l,r))
    return merged


def window_coverage(v,pair,l,r):
    times=event_times(v,l,r)
    witnesses=[]
    patchers=set()
    for t in times:
        blockers=[i for i,d in enumerate(v) if distance(d*t)<H]
        assert not (set(blockers)&set(pair))
        patchers.update(blockers)
        if not blockers:
            witnesses.append(t)
    for x,y in zip(times,times[1:]):
        blockers=[i for i,d in enumerate(v) if distance(d*(x+y)/2)<H]
        assert not (set(blockers)&set(pair))
        patchers.update(blockers)
    return {'left':l,'right':r,'patchers':sorted(patchers),
            'fully_covered':not witnesses,'first_clear':min(witnesses) if witnesses else None}


def surviving_return_analysis(v,tr,ret):
    p,q=ret['steps']
    start=tr['rows'][p]['time']
    repeat=tr['rows'][q]['time']
    period=repeat-start
    pair=ret['pair']
    assert all((v[i]*period).denominator==1 for i in pair)
    windows=clear_pair_windows(v,pair,start,repeat)
    coverage=[]
    for l,r in windows:
        old=window_coverage(v,pair,l,r)
        new=window_coverage(v,pair,l+period,r+period)
        assert old['fully_covered']
        coverage.append({'first_period':old,'second_period':new})
    return {'pair':pair,'start_step':p,'repeat_step':q,'period':period,
        'phase_advances':[d*period for d in v],
        'blockers_at_returns':[tr['rows'][p]['blockers'],tr['rows'][q]['blockers']],
        'blockers_after_pair_exits':[tr['rows'][p+1]['blockers'],tr['rows'][q+1]['blockers']],
        'pair_clear_windows':coverage}


def verify_resonant_gap_region(v,tr):
    m,p,q,a,b,c,f=v
    D=a/4
    assert b==5*D
    assert c>0
    assert 9*c<=65*m<=15*c
    assert 25*c<=65*p<=31*c
    assert 33*c<=65*q<=39*c
    assert 57*c<=325*D and 260*D<=47*c
    assert 81*c<=65*f<=87*c
    witness=F(65,8)/c
    assert tr['rows'][-1]['time']==witness
    assert all(distance(d*witness)>=H for d in v)
    return {'D':D,'c':c,'witness':witness,'lean_region_conditions':True}


def run(source, output):
    with open(source) as f:
        data=json.load(f)
    counts=Counter()
    experiments=[]
    seen=set()
    for path in data['paths']:
        a=list(map(F,path['a']))
        b=list(map(F,path['b']))
        for cell in path['cells']:
            z=F(cell['sample'])
            v=[x+y*z for x,y in zip(a,b)]
            for old in cell['returns']:
                i,j=old['pair']
                r,s=old['lap_advance']
                target=v[i]*F(s,r)
                key=(tuple(v),i,j,r,s)
                if key in seen:
                    continue
                seen.add(key)
                counts['observed_return_targets']+=1
                u=list(v)
                u[j]=target
                if len(set(u))<7:
                    counts['resonance_collides_speeds']+=1
                    continue
                tr=trace(u,[F(0)]*7,F(0),F(-1),F(1))
                assert tr['status']=='clear',tr['status']
                counts['valid_resonance_tests']+=1
                rec=recurrence_records(u,tr)
                matching=[e for e in rec if e['pair']==[i,j]]
                same=[e for e in matching if e['depth_drift']==0]
                pair_rows=[k for k,row in enumerate(tr['rows']) if row['source']==i and row.get('winner')==j]
                if same:
                    category='zero_drift_return_survives'
                    verified_region=verify_resonant_gap_region(u,tr)
                elif matching:
                    category='pair_returns_with_changed_pattern'
                elif pair_rows:
                    category='pair_occurs_once'
                else:
                    category='pair_absent'
                counts[category]+=1
                counts['other_zero_drift_returns']+=sum(e['depth_drift']==0 and e['pair']!=[i,j] for e in rec)
                experiments.append({'source':path['seed'],'original_speeds':v,
                    'original_return':old,'changed_runner':j,'change':target-v[j],
                    'resonant_speeds':u,'category':category,'pair_rows':pair_rows,
                    'trace':compact_trace(tr),'returns':rec,
                    'zero_drift_analysis':[surviving_return_analysis(u,tr,e) for e in same],
                    'verified_region':verified_region if same else None})
    # Follow the complete interval to a few closest distinct resonances. The
    # partition detects intermediate handoff changes, not just endpoint outcomes.
    counts['distinct_resonant_speed_sets']=len({tuple(e['resonant_speeds']) for e in experiments})
    closest=sorted(experiments,key=lambda e:abs(e['change']))
    paths=[]
    for e in closest[:8]:
        v=e['original_speeds']
        direction=[F(0)]*7
        direction[e['changed_runner']]=e['change']
        cells,bounds,inc=partition(v,direction,F(0),F(1),max_cells=1000)
        paths.append({'original_speeds':v,'direction':direction,
            'target_pair':e['original_return']['pair'],'target_lap_advance':e['original_return']['lap_advance'],
            'incomplete':inc,'cells':[{k:x for k,x in c.items() if k!='trace'} |
                {'trace':compact_trace(c['trace'])} for c in cells],
            'boundaries':[{k:x for k,x in bd.items() if k!='trace'} |
                ({'trace':compact_trace(bd['trace'])} if 'trace' in bd else {}) for bd in bounds]})
        counts['path_cells']+=len(cells)
        counts['path_boundaries']+=len(bounds)
        counts['incomplete_path_intervals']+=len(inc)
    # Also follow a complete deformation from the AP, rather than only a
    # small neighborhood, to a surviving resonance.
    survivor=next(e for e in closest if e['category']=='zero_drift_return_survives')
    ap=list(map(F,range(1,8)))
    direction=[y-x for x,y in zip(ap,survivor['resonant_speeds'])]
    cells,bounds,inc=partition(ap,direction,F(0),F(1),max_cells=2000)
    deformation={'start':ap,'end':survivor['resonant_speeds'],'incomplete':inc,
        'cells':[{k:x for k,x in c.items() if k!='trace'} |
            {'trace':compact_trace(c['trace'])} for c in cells],
        'boundaries':[{k:x for k,x in bd.items() if k!='trace'} |
            ({'trace':compact_trace(bd['trace'])} if 'trace' in bd else {}) for bd in bounds]}
    counts['ap_deformation_cells']=len(cells)
    counts['ap_deformation_boundaries']=len(bounds)
    counts['ap_deformation_incomplete']=len(inc)
    result={'method':__doc__,'summary':dict(counts),'experiments':experiments,'paths_to_resonance':paths}
    result['ap_to_resonance']=deformation
    with open(output,'w') as f:
        json.dump(result,f,default=frac,indent=2)
    examples={}
    for e in closest:
        examples.setdefault(e['category'],{k:v for k,v in e.items() if k!='trace'})
    print(json.dumps({'summary':dict(counts),'examples':examples},default=frac,indent=2))


class Tests(unittest.TestCase):
    def test_pair_period(self):
        windows=clear_pair_windows([F(4),F(5)],[0,1],F(9,40),F(49,40))
        shifted=clear_pair_windows([F(4),F(5)],[0,1],F(49,40),F(89,40))
        self.assertEqual(len(windows),6)
        self.assertEqual([(l+1,r+1) for l,r in windows],shifted)

    def test_surviving_zero_drift(self):
        v=list(map(F,['1','23509/10000','8103/2500','52223/12500',
                      '52223/10000','57871/10000','17184527/2310000']))
        tr=trace(v,[F(0)]*7,F(0),F(-1),F(1))
        self.assertEqual(tr['steps'],25)
        rec=[r for r in recurrence_records(v,tr) if r['depth_drift']==0]
        self.assertEqual(len(rec),1)
        self.assertEqual(rec[0]['steps'],[3,21])
        analysis=surviving_return_analysis(v,tr,rec[0])
        self.assertTrue(all(w['first_period']['fully_covered'] for w in analysis['pair_clear_windows']))
        self.assertFalse(analysis['pair_clear_windows'][1]['second_period']['fully_covered'])
        self.assertEqual(analysis['pair_clear_windows'][1]['second_period']['first_clear'],F(81250,57871))
        verify_resonant_gap_region(v,tr)


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--source',default='experiments/nN/redo/handoff_boundaries_v1.json')
    p.add_argument('--output',default='experiments/nN/redo/zero_drift_handoffs_v1.json')
    p.add_argument('--test',action='store_true')
    args=p.parse_args()
    if args.test:
        unittest.main(argv=[__file__])
    else:
        run(args.source,args.output)
