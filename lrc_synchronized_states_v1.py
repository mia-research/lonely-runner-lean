from fractions import Fraction

def is_blocking(frac_part, blocking_intervals=None):
    """Check if a fractional part is blocking.
    Blocking means in [0, 1/11) ∪ (10/11, 1)
    """
    if blocking_intervals is None:
        blocking_intervals = [Fraction(0), Fraction(1, 11), Fraction(10, 11), Fraction(1)]
    
    # in [0, 1/11)
    if Fraction(0) <= frac_part < Fraction(1, 11):
        return True
    # in (10/11, 1)
    if Fraction(10, 11) < frac_part < Fraction(1):
        return True
    return False

def question_1():
    """
    For each k=1,...,8, compute {p * (11k+12) / 121} (mod 1) for p ∈ {6,7,8,9,10,11}.
    Identify blocking runners.
    """
    print("=" * 80)
    print("QUESTION 1: Blocking runners at start of I_{k+1}")
    print("=" * 80)
    print()
    
    results = {}
    
    for k in range(1, 9):  # k = 1, 2, ..., 8
        ik_start = Fraction(11 * k + 12, 121)  # Start of I_{k+1}
        print(f"k = {k}: I_{{{k+1}}} starts at {ik_start} = {float(ik_start):.6f}")
        print("-" * 80)
        
        blocking_runners = []
        runner_states = {}
        
        for p in [6, 7, 8, 9, 10, 11]:
            position_unnorm = p * ik_start
            position = position_unnorm % 1  # Fractional part
            
            is_block = is_blocking(position)
            runner_states[p] = {
                'numerator': position.numerator,
                'denominator': position.denominator,
                'fraction': position,
                'decimal': float(position),
                'blocking': is_block
            }
            
            if is_block:
                blocking_runners.append(p)
            
            blocking_str = "BLOCKING" if is_block else "  clear  "
            print(f"  p={p:2d}: {{p * (11k+12)/121}} = {str(position):>20s} = {float(position):9.6f}  [{blocking_str}]")
        
        print()
        results[k] = {
            'ik_start': ik_start,
            'blocking_runners': blocking_runners,
            'runner_states': runner_states
        }
    
    print()
    print("SUMMARY TABLE: Blocking runners by k")
    print("-" * 80)
    for k in range(1, 9):
        blocking = results[k]['blocking_runners']
        print(f"  k={k}: Blocking runners = {blocking}")
    
    return results

def question_2():
    """
    For each runner p with gcd(p,11)=1, the step is r/11 where r = p mod 11.
    Over 8 consecutive steps, at most how many fall in [0,1/11) ∪ (10/11,1)?
    """
    print()
    print("=" * 80)
    print("QUESTION 2: Maximum blocking hits over 8 steps")
    print("=" * 80)
    print()
    
    import math
    
    # For runners in CCL {6,7,8,9,10} and also 11 (which is handled specially)
    # But we do the general computation for r = 1,...,10
    
    summary_stats = {}
    
    for r in range(1, 11):
        step = Fraction(r, 11)
        
        # Simulate 8 consecutive steps starting from some initial position
        # We'll start from position 0 and apply steps r/11 eight times
        blocking_count = 0
        blocking_steps = []
        
        print(f"r = {r:2d} (step = {step}):")
        print("  Steps from k=1 to k=8:")
        
        for k in range(1, 9):
            # Position after k steps: k * r/11 (mod 1)
            position = (k * step) % 1
            is_block = is_blocking(position)
            
            if is_block:
                blocking_count += 1
                blocking_steps.append(k)
            
            blocking_str = "BLOCKING" if is_block else "clear"
            print(f"    k={k}: position = {str(position):>20s} = {float(position):9.6f}  [{blocking_str}]")
        
        print(f"  Total blocking hits in 8 steps: {blocking_count}")
        print(f"  Blocking at steps: {blocking_steps}")
        print()
        
        summary_stats[r] = {
            'step': step,
            'blocking_count': blocking_count,
            'blocking_steps': blocking_steps,
            'max_blocking': blocking_count
        }
    
    print()
    print("SUMMARY: Max blocking hits per r value")
    print("-" * 80)
    for r in range(1, 11):
        stats = summary_stats[r]
        print(f"  r={r:2d}: {stats['blocking_count']} hits (max over 8 steps)")
    
    print()
    print("OVERALL STATISTIC:")
    max_over_all_r = max(summary_stats[r]['blocking_count'] for r in range(1, 11))
    print(f"  Maximum blocking hits over all r ∈ {{1,...,10}} and 8 consecutive steps: {max_over_all_r}")
    
    return summary_stats

if __name__ == '__main__':
    print("\n")
    print("█" * 80)
    print("LRC SYNCHRONIZED STATES: Runner Position Analysis for n=11")
    print("█" * 80)
    print("\n")
    
    q1_results = question_1()
    q2_results = question_2()
    
    print("\n")
    print("█" * 80)
    print("ANALYSIS COMPLETE")
    print("█" * 80)
    print("\n")
    
    # Save results to a summary file
    summary_file = "/Users/trentpalelei/Desktop/Math Ex/lrc_synchronized_states_summary.txt"
    with open(summary_file, 'w') as f:
        f.write("LRC SYNCHRONIZED STATES: Runner Position Analysis for n=11\n")
        f.write("=" * 80 + "\n\n")
        
        f.write("QUESTION 1: Blocking runners at start of I_{k+1}\n")
        f.write("-" * 80 + "\n")
        for k in range(1, 9):
            blocking = q1_results[k]['blocking_runners']
            f.write(f"k={k}: Blocking runners = {blocking}\n")
        
        f.write("\n")
        f.write("QUESTION 2: Maximum blocking hits over 8 steps\n")
        f.write("-" * 80 + "\n")
        for r in range(1, 11):
            f.write(f"r={r:2d}: {q2_results[r]['blocking_count']} hits\n")
        
        max_hits = max(q2_results[r]['blocking_count'] for r in range(1, 11))
        f.write(f"\nOverall maximum blocking hits: {max_hits}\n")
    
    print(f"Summary saved to: {summary_file}")
