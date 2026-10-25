"""Check emitted judgments in Agda, bisecting failing batches (untrusted driver).

run_agda.py OUTDIR [BATCH] [JOBS]
"""
import sys, os, pickle, subprocess, re
from concurrent.futures import ThreadPoolExecutor

outdir = sys.argv[1]
batch = int(sys.argv[2]) if len(sys.argv) > 2 else 64
jobs = int(sys.argv[3]) if len(sys.argv) > 3 else 4
items = [x for x in pickle.load(open(os.path.join(outdir, 'items.pkl'), 'rb')) if x[2]]
HEADER = '{-# OPTIONS --cubical #-}\nmodule %s where\nopen import HornPrelude\nopen import HornDefs\n\n'
results = {}


def agda(group):
    name = 'B' + '_'.join(str(n) for n, *_ in group[:1]) + f'x{len(group)}'
    path = os.path.join(outdir, name + '.agda')
    open(path, 'w').write(HEADER % name + '\n'.join(d for _, _, d, _ in group))
    try:
        p = subprocess.run(['bash', '-c', f'ulimit -v 11000000; agda --no-libraries {name}.agda'],
                           cwd=outdir, capture_output=True, text=True, timeout=900)
        ok, msg = p.returncode == 0, p.stdout + p.stderr
    except subprocess.TimeoutExpired:
        ok, msg = False, 'TIMEOUT'
    os.remove(path)
    if os.path.exists(path + 'i'):
        os.remove(path + 'i')
    return ok, msg


def check(group):
    ok, msg = agda(group)
    if ok:
        for n, label, _, _ in group:
            results[n] = (label, 'pass', '')
        return
    if len(group) == 1 or 'TIMEOUT' in msg:
        if len(group) > 1:
            mid = len(group) // 2
            check(group[:mid]); check(group[mid:])
            return
        n, label, _, _ = group[0]
        lines = [l for l in msg.splitlines() if not l.strip().startswith('Checking')]
        results[n] = (label, 'fail', '\n'.join(lines[:12]))
        return
    mid = len(group) // 2
    check(group[:mid]); check(group[mid:])


groups = [items[i:i + batch] for i in range(0, len(items), batch)]
with ThreadPoolExecutor(jobs) as ex:
    list(ex.map(check, groups))
pickle.dump(results, open(os.path.join(outdir, 'results.pkl'), 'wb'))
print(sum(1 for r in results.values() if r[1] == 'pass'), 'pass,',
      sum(1 for r in results.values() if r[1] == 'fail'), 'fail')
