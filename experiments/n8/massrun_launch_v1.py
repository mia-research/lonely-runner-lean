# massrun_launch_v1.py -- daemonize both mass-run drivers (double-fork, E911 pattern):
#   fine-ladder: m4rung2_batch1_driver.py with massrun_fine_selection.json (200 boxes)
#   C3:          m4fix_driver.py            with massrun_c3_selection.json  (200 boxes)
# Usage: python3 -I massrun_launch_v1.py [fine|c3|both]
import json, os, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))


def sel_args(tag):
    sel = json.load(open(os.path.join(HERE, 'massrun_%s_selection_b2.json' % tag)))
    return ['%s' % ','.join(str(x) for x in b) for b in sel['selection']], len(sel['selection'])


def daemonize(argv, log):
    """Double-fork: child detaches into its own session, stdout/stderr -> log."""
    logf = open(log, 'ab', buffering=0)
    pid = os.fork()
    if pid == 0:                      # first child
        os.setsid()
        pid2 = os.fork()
        if pid2 == 0:                 # second child: exec the driver
            os.dup2(logf.fileno(), 1)
            os.dup2(logf.fileno(), 2)
            os.execvp(argv[0], argv)
        os._exit(0)                   # first child exits immediately
    os.waitpid(pid, 0)
    logf.close()
    return pid


def main():
    which = sys.argv[1] if len(sys.argv) > 1 else 'both'
    jobs = []
    if which in ('fine', 'both'):
        args, n = sel_args('fine')
        jobs.append(('fine',
                     [sys.executable, '-I', os.path.join(HERE, 'massrun_fine_driver_v2.py')],
                     n, os.path.join(HERE, 'massrun_fine_driver.out')))
    if which in ('c3', 'both'):
        args, n = sel_args('c3')
        jobs.append(('c3',
                     [sys.executable, '-I', os.path.join(HERE, 'm4fix_driver.py')] + args,
                     n, os.path.join(HERE, 'massrun_c3_driver.out')))
    for tag, argv, n, log in jobs:
        daemonize(argv, log)
        print('%s driver daemonized: %d boxes, log %s' % (tag, n, os.path.basename(log)),
              flush=True)
    time.sleep(20)
    for tag, _, _, log in jobs:
        try:
            tail = open(log).read().strip().splitlines()[-3:]
            print('--- %s log tail:' % tag, flush=True)
            for l in tail:
                print('    ' + l, flush=True)
        except Exception as e:
            print('--- %s log read failed: %s' % (tag, e), flush=True)


if __name__ == '__main__':
    main()
