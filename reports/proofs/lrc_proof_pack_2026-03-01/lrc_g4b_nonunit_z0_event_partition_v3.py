#!/usr/bin/env python3
"""
Post-process v2 leave-certifier rows into event-level partition:
- event key: (n, tuple_id, component_id, run_id, b_star)
- classify events as:
  A) pure_nonunit: nonunit z0 present, unit z0 count == 0
  B) mixed: nonunit z0 present, unit z0 count > 0

For each event with nonunit z0 candidates, compute existential witness:
  exists e in nonunit_z0 such that leave_pass(e)=1.

Writes:
  /tmp/lrc_g4b_nonunit_z0_event_rows_v3.csv
  /tmp/lrc_g4b_nonunit_z0_event_summary_v3.md
"""
from __future__ import annotations

import csv
from collections import defaultdict
from pathlib import Path

IN_ROWS = Path('/Users/trentpalelei/Desktop/Math Ex/reports/proofs/lrc_proof_pack_2026-03-01/lrc_g4b_nonunit_z0_leave_rows_v2.csv')
OUT_ROWS = Path('/tmp/lrc_g4b_nonunit_z0_event_rows_v3.csv')
OUT_SUMM = Path('/tmp/lrc_g4b_nonunit_z0_event_summary_v3.md')


def main() -> int:
    rows = []
    with IN_ROWS.open() as f:
        r = csv.DictReader(f)
        rows = list(r)

    by_event = defaultdict(list)
    for x in rows:
        if int(x['is_boundary_end']) == 1:
            continue
        key = (x['n'], x['tuple_id'], x['component_id'], x['run_id'], x['b_star'])
        by_event[key].append(x)

    event_rows = []
    for key, rs in by_event.items():
        n, tid, cid, rid, bstar = key
        e_tuple = rs[0]['e_tuple']
        L = rs[0]['L']
        run_start = rs[0]['run_start_b']
        run_end = rs[0]['run_end_b']
        run_len = rs[0]['run_len']
        D_star = rs[0]['D_star']

        cand = [z for z in rs if int(z['filtered_nonunit_event']) == 1]
        if not cand:
            continue

        unit_z0 = max(int(z['z0_unit_at_bstar']) for z in rs)
        nonunit_ct = len(cand)
        pass_any = int(any(int(z['leave_pass']) == 1 for z in cand))
        fail_all = int(pass_any == 0)
        empty_all = int(all(int(z['leave_size']) == 0 for z in cand))
        any_snatch = int(any((int(z['leave_size']) > 0 and int(z['leave_pass']) == 0) for z in cand))

        class_tag = 'pure_nonunit' if unit_z0 == 0 else 'mixed_unit_nonunit'

        first_pass = ''
        for z in cand:
            if int(z['leave_pass']) == 1:
                first_pass = f"e={z['e_target']},g={z['g_e']},w={z['witness_count']}"
                break
        first_fail = ''
        for z in cand:
            if int(z['leave_pass']) == 0:
                first_fail = f"e={z['e_target']},g={z['g_e']},leave={z['leave_size']}"
                break

        event_rows.append({
            'n': n,
            'tuple_id': tid,
            'e_tuple': e_tuple,
            'L': L,
            'component_id': cid,
            'run_id': rid,
            'run_start_b': run_start,
            'run_end_b': run_end,
            'run_len': run_len,
            'b_star': bstar,
            'D_star': D_star,
            'class_tag': class_tag,
            'unit_z0_count': unit_z0,
            'nonunit_candidate_count': nonunit_ct,
            'existential_pass': pass_any,
            'all_fail': fail_all,
            'all_leave_empty': empty_all,
            'any_snatch_fail': any_snatch,
            'first_pass': first_pass,
            'first_fail': first_fail,
        })

    # write event rows
    with OUT_ROWS.open('w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=list(event_rows[0].keys()) if event_rows else [])
        if event_rows:
            w.writeheader()
            w.writerows(event_rows)

    # summarize
    def stats(sub):
        tot = len(sub)
        ok = sum(int(x['existential_pass']) for x in sub)
        fail = tot - ok
        empty = sum(int(x['all_leave_empty']) for x in sub)
        sn = sum(int(x['any_snatch_fail']) for x in sub)
        pct = (100.0 * ok / tot) if tot else 0.0
        return tot, ok, fail, empty, sn, pct

    all_tot, all_ok, all_fail, all_empty, all_sn, all_pct = stats(event_rows)
    pure = [x for x in event_rows if x['class_tag'] == 'pure_nonunit']
    mix = [x for x in event_rows if x['class_tag'] == 'mixed_unit_nonunit']
    p_tot, p_ok, p_fail, p_empty, p_sn, p_pct = stats(pure)
    m_tot, m_ok, m_fail, m_empty, m_sn, m_pct = stats(mix)

    lines = []
    lines.append('# Non-Unit z0 Event Partition Summary v3')
    lines.append('Date: 2026-03-05')
    lines.append('')
    lines.append('## Definitions')
    lines.append('- Event key: `(n, tuple_id, component_id, run_id, b_star)` for interior run exits.')
    lines.append('- Candidate set: non-unit z0 runners at `b_star` from v2 rows.')
    lines.append('- Existential pass: `exists candidate e with leave_pass(e)=1`.')
    lines.append('')
    lines.append('## Counts')
    lines.append(f'- all events with non-unit candidates: {all_tot}')
    lines.append(f'- pure_nonunit events: {p_tot}')
    lines.append(f'- mixed_unit_nonunit events: {m_tot}')
    lines.append('')
    lines.append('## Results')
    lines.append('| Class | Events | Existential Pass | Rate | All-Fail | All-Leave-Empty | Any-Snatch-Fail |')
    lines.append('|---|---:|---:|---:|---:|---:|---:|')
    lines.append(f'| all | {all_tot} | {all_ok} | {all_pct:.1f}% | {all_fail} | {all_empty} | {all_sn} |')
    lines.append(f'| pure_nonunit | {p_tot} | {p_ok} | {p_pct:.1f}% | {p_fail} | {p_empty} | {p_sn} |')
    lines.append(f'| mixed_unit_nonunit | {m_tot} | {m_ok} | {m_pct:.1f}% | {m_fail} | {m_empty} | {m_sn} |')
    lines.append('')
    lines.append('## Interpretation')
    lines.append('- Pure non-unit exits isolate the non-unit mechanism.')
    lines.append('- Mixed exits should be routed to the unit-z0 already-proved branch when non-unit candidate is non-causal (`leave_empty`).')
    lines.append('')
    lines.append('## Mixed all-fail samples')
    mixed_fail = [x for x in mix if int(x['existential_pass']) == 0]
    if not mixed_fail:
        lines.append('- none')
    else:
        for x in mixed_fail[:12]:
            lines.append(
                '- '
                f"n={x['n']} E=({x['e_tuple']}) b*={x['b_star']} run=[{x['run_start_b']},{x['run_end_b']}] "
                f"unit_z0={x['unit_z0_count']} nonunit_ct={x['nonunit_candidate_count']} "
                f"first_fail={x['first_fail']}"
            )

    OUT_SUMM.write_text('\n'.join(lines) + '\n')

    print(f'wrote: {OUT_ROWS} ({len(event_rows)} events)')
    print(f'wrote: {OUT_SUMM}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
