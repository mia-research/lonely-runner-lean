#!/usr/bin/env python3
"""Driver for the Localized Bit Extraction battery.
Spec: PREREG_localized_bit_extraction_v1.md + _DEVIATIONS.md (D1: replicate across PRIMES only)."""
import pickle
import sys
import time
import numpy as np
sys.path.insert(0, '/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation')
from lbe_harness_v1 import *

DECADES = [(120, 400), (1000, 1600), (10000, 10600), (46000, 46600), (100000, 100600)]


def main():
    curves = []
    for lo, hi in DECADES:
        t0 = time.time()
        r = prime_order_curve(lo, hi)
        if r is None:
            print('no curve in', lo, hi, flush=True)
            continue
        print('curve p=%d n=%d  (%.1fs)' % (r[0], r[1], time.time() - t0), flush=True)
        curves.append(r)

    recs = []
    for (p, n, G) in curves:
        t0 = time.time()
        nd = 200 if n < 20000 else 80          # null draws; cost scales with n
        rec = run_prime(p, n, G, ndraw=nd)
        rec['secs'] = time.time() - t0
        rec['ndraw'] = nd
        summarize(rec)
        print('   [%.1fs, ndraw=%d]' % (rec['secs'], nd), flush=True)
        if rec['status'] == 'ok':
            print('   corrected: Holm=%d BH=%d  omnibus=%.1f/%d P=%.3g'
                  % (rec['n_holm_corr'], rec['n_bh_corr'], rec['omnibus_corr'][0],
                     rec['omnibus_corr'][1], rec['omnibus_corr'][2]), flush=True)
            print('   forced-null fire (corrected):', rec['forced_fire_corr'], flush=True)
            top = sorted(rec['cells'], key=lambda c: c['P_corr'])[:6]
            for c in top:
                print('     %-16s x %-8s P=%.3g Pc=%.3g emp=%.3g V=%.4f'
                      % (c['F'], c['T'], c['P'], c['P_corr'], c['emp_p'], c['V']), flush=True)
        recs.append(rec)
        with open('lbe_results_v1.pkl', 'wb') as fh:
            pickle.dump([{k: v for k, v in r.items() if k != 'cal'} for r in recs], fh)

    # ---------- replication tally across primes (DEVIATION D1: primes only)
    print('\n' + '=' * 92)
    print('REPLICATION TALLY across %d primes (uncorrected P<0.01), DEVIATION D1' % len(recs))
    ok = [r for r in recs if r['status'] == 'ok']
    tally = {}
    for r in ok:
        for c in r['cells']:
            tally.setdefault((c['F'], c['T']), []).append((r['p'], c['P'], c['P_corr'], c['V']))
    rows = []
    for k, v in tally.items():
        fires = sum(1 for (_, P, _, _) in v if P < 0.01)
        if fires >= 2:
            rows.append((fires, k, v))
    rows.sort(key=lambda t: -t[0])
    for fires, k, v in rows[:25]:
        print('  %-16s x %-8s  fires %d/%d   %s'
              % (k[0], k[1], fires, len(v),
                 ' '.join('p%d:%.2g' % (p, P) for (p, P, _, _) in v)))
    if not rows:
        print('  (no cell fires at uncorrected P<0.01 in >=2 primes)')
    print('\nPOWER (e_min per prime):', {r['p']: r.get('e_min') for r in ok})
    print('OMNIBUS per prime:', {r['p']: round(r['omnibus_corr'][2], 4) for r in ok})
    print('HOLM per prime:', {r['p']: r['n_holm_corr'] for r in ok})


if __name__ == '__main__':
    main()
