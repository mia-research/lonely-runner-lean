"""
Transfer-depth scan for the dropped-unit thin-burden chain.

For each dropped-unit Case-2 tuple with full coverage at b_0 = L/n,
traces the thin-burden chain:
  (r*_0, e*_0, b_0) -> (r*_1, e*_1, b_1) -> ... -> safe fibre

Records the chain length histogram and prints all cases where chain_depth > 2.

Scan scope:
  n in {5, 6, 7, 8}  with speeds in {1, ..., 3n} for n<=6, {1, ..., 2n} for n>=7
"""

from __future__ import annotations
from math import gcd, lcm
from itertools import combinations
from collections import defaultdict


def inv_mod(a: int, n: int) -> int:
    return pow(a, -1, n)


def bad_set(e: int, b: int, L: int, n: int) -> set[int]:
    """Returns bad(e, floor(eb/L), n) as a set of residues in Z_n."""
    t = (e * b) // L
    rho = e % n
    out: set[int] = set()
    for r in range(n):
        if (rho * r + t) % n == 0 or (rho * r + t + 1) % n == 0:
            out.add(r)
    return out


def coverage_union(E_non: list[int], b: int, L: int, n: int) -> set[int]:
    union: set[int] = set()
    for e in E_non:
        union |= bad_set(e, b, L, n)
    return union


def multiplicities_at(E_non: list[int], b: int, L: int, n: int) -> dict[int, list[int]]:
    """Returns {residue: [list of runners covering it]} at fibre b."""
    cover: dict[int, list[int]] = defaultdict(list)
    for e in E_non:
        for r in bad_set(e, b, L, n):
            cover[r].append(e)
    return dict(cover)


def floor_reset_events(E_non: list[int], b0: int, b_upper: int, L: int) -> list[tuple[int, int]]:
    """Return sorted list of (fibre, runner) for all floor-reset events in (b0, b_upper]."""
    events = []
    for e in E_non:
        t_start = (e * b0) // L
        t_end = (e * b_upper) // L
        for t in range(t_start + 1, t_end + 1):
            b_event = (t * L) // e
            if b_event > b0 and b_event <= b_upper:
                events.append((b_event, e))
    return sorted(set(events))


def trace_thin_burden_chain(E_non: list[int], b0: int, b_upper: int, L: int, n: int) -> dict:
    """
    Starting from b0, find the thin (multiplicity-1) residue, then trace its chain
    of burden migrations until a safe fibre is found or b_upper is reached.

    Returns a dict with:
      'initial_thin': (residue, sole_cover_runner) or None
      'chain': list of (residue, sole_cover, event_b)
      'safe_b': the first safe fibre found (None if not found in range)
      'safe_missing': the missing residue at the safe fibre
      'chain_depth': number of transfers before safe fibre (0 = direct exposure)
    """
    cover0 = multiplicities_at(E_non, b0, L, n)
    union0 = set(cover0.keys())
    if len(union0) < n:
        return {'initial_thin': None, 'chain': [], 'safe_b': b0, 'safe_missing': sorted(set(range(n)) - union0), 'chain_depth': -1}

    # Find multiplicity-1 residues at b0
    thin_residues = [(r, runners[0]) for r, runners in cover0.items() if len(runners) == 1]
    if not thin_residues:
        return {'initial_thin': None, 'chain': [], 'safe_b': None, 'safe_missing': None, 'chain_depth': None}

    # Track the first-found thin residue
    r_star, e_star = thin_residues[0]

    events = floor_reset_events(E_non, b0, b_upper, L)

    chain = [(r_star, e_star, b0)]
    current_r = r_star
    current_e = e_star

    # Walk through events that affect current_r or current_e
    for (b_ev, e_runner) in events:
        # Check the interval just before this event: is current_r still multiplicity 1?
        # (Bad sets are constant between events, so just check at b_ev - 1 or at b0 between events)
        # Actually check at b_ev (the event itself changes the bad set of e_runner)
        # Check just before: b_ev - 1 (if b_ev > b0 + 1) or b0
        b_check = b_ev - 1 if b_ev > b0 + 1 else b0
        union_before = coverage_union(E_non, b_check, L, n)
        if len(union_before) < n:
            # Already a safe fibre before this event - but we should have caught it
            # Search more carefully
            break

        # Check coverage just AFTER this event (at b_ev)
        union_after = coverage_union(E_non, b_ev, L, n)
        if len(union_after) < n:
            missing = sorted(set(range(n)) - union_after)
            return {
                'initial_thin': (r_star, e_star),
                'chain': chain,
                'safe_b': b_ev,
                'safe_missing': missing,
                'chain_depth': len(chain) - 1,
            }

        # Check if current_r's coverage changed
        cover_after = multiplicities_at(E_non, b_ev, L, n)
        cover_list_after = cover_after.get(current_r, [])
        if len(cover_list_after) == 0:
            # Exposed! This is a safe fibre for b with b ≡ current_r (mod n) near b_ev
            # Find first b in [b_ev, b_ev+n) with b ≡ current_r (mod n)
            safe_b = b_ev + (current_r - b_ev % n) % n
            if safe_b > b_upper:
                safe_b = b_ev
            return {
                'initial_thin': (r_star, e_star),
                'chain': chain,
                'safe_b': safe_b,
                'safe_missing': [current_r],
                'chain_depth': len(chain) - 1,
            }
        elif len(cover_list_after) == 1:
            new_e = cover_list_after[0]
            if new_e != current_e:
                # Burden transferred to new runner
                chain.append((current_r, new_e, b_ev))
                current_e = new_e
        # If multiplicity increased: no longer thin, but we continue tracking
        # (the thin burden may migrate to a new residue through other events)

    # Fallback: do a direct scan for first safe fibre
    for b in range(b0, b_upper + 1):
        union = coverage_union(E_non, b, L, n)
        if len(union) < n:
            missing = sorted(set(range(n)) - union)
            return {
                'initial_thin': (r_star, e_star),
                'chain': chain,
                'safe_b': b,
                'safe_missing': missing,
                'chain_depth': len(chain) - 1,
            }

    return {
        'initial_thin': (r_star, e_star),
        'chain': chain,
        'safe_b': None,
        'safe_missing': None,
        'chain_depth': None,
    }


def enumerate_dropped_unit_tuples(n: int, max_speed: int) -> list[tuple]:
    """
    Enumerate Case-2 tuples: gcd(E)=1, at least one speed divisible by n,
    n-1 speeds total, at least one unit residue class absent from R_non.
    Returns list of E tuples.
    """
    speeds = list(range(1, max_speed + 1))
    results = []
    for combo in combinations(speeds, n - 1):
        if gcd(*combo) != 1:
            continue
        if not any(e % n == 0 for e in combo):
            continue
        E_non = [e for e in combo if e % n != 0]
        R_non = {e % n for e in E_non}
        units = {r for r in range(1, n) if gcd(r, n) == 1}
        missing_units = units - R_non
        if missing_units:
            results.append(combo)
    return results


def scan_n(n: int, max_speed: int) -> dict:
    """Run the scan for a single n value."""
    tuples = enumerate_dropped_unit_tuples(n, max_speed)
    depth_histogram: dict[int | None, int] = defaultdict(int)
    deep_cases = []
    fully_covered_count = 0
    total = len(tuples)

    for E in tuples:
        L = 1
        for e in E:
            L = lcm(L, e)
        b0 = L // n
        b_upper = ((n - 1) * L) // n
        E_non = [e for e in E if e % n != 0]

        # Check if b0 is fully covered
        union0 = coverage_union(E_non, b0, L, n)
        if len(union0) < n:
            # Not fully covered at b0 - safe fibre exists immediately
            depth_histogram[-1] += 1
            continue

        fully_covered_count += 1
        result = trace_thin_burden_chain(E_non, b0, b_upper, L, n)
        depth = result['chain_depth']
        depth_histogram[depth] += 1

        if depth is not None and depth > 2:
            deep_cases.append({'n': n, 'E': E, 'result': result})

    return {
        'n': n,
        'max_speed': max_speed,
        'total_tuples': total,
        'fully_covered_at_b0': fully_covered_count,
        'depth_histogram': dict(depth_histogram),
        'deep_cases': deep_cases,
    }


def main():
    configs = [(5, 15), (6, 18), (7, 14), (8, 16)]
    for n, max_speed in configs:
        print(f"\n=== n={n}, speeds <= {max_speed} ===")
        result = scan_n(n, max_speed)
        print(f"Total dropped-unit tuples: {result['total_tuples']}")
        print(f"Fully covered at b0:       {result['fully_covered_at_b0']}")
        print(f"Depth histogram (depth -> count):")
        for depth in sorted(k for k in result['depth_histogram'] if k is not None):
            print(f"  depth {depth}: {result['depth_histogram'][depth]}")
        if None in result['depth_histogram']:
            print(f"  depth None (no safe fibre found): {result['depth_histogram'][None]}")
        if result['deep_cases']:
            print(f"DEEP CASES (depth > 2):")
            for case in result['deep_cases'][:5]:
                print(f"  E={case['E']}, depth={case['result']['chain_depth']}, safe_b={case['result']['safe_b']}")
        else:
            print("  No deep cases (all chains depth <= 2)")


if __name__ == "__main__":
    main()
