"""Per-rule summary over all runs (untrusted research tool).

summary.py MODE K [WORKDIR]   (MODE: comp or transp)
"""
import sys, os, pickle, glob
from collections import defaultdict
S = sys.argv[3] if len(sys.argv) > 3 else os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from expand import parse_all

mode, k = sys.argv[1], sys.argv[2]
GEN = ('def/', 'ty/', 'ctor/', 'elim/')


def generated(r):
    return any(g in r for g in GEN)


core = set()
for th in glob.glob(f'{S}/c/*/theory.horn'):
    for f in parse_all(open(th).read()):
        if f[0] == 'rule' and not generated(f[1]):
            core.add(f[1])
agda = defaultdict(lambda: [0, 0])
fails = defaultdict(list)
for d in glob.glob(f'{S}/runs/*-{k}' + ('-transp' if mode == 'transp' else '')):
    n = os.path.basename(d).rsplit('-', 2 if mode == 'transp' else 1)[0]
    rp = os.path.join(d, 'results.pkl')
    if not os.path.exists(rp):
        continue
    for _, (label, st, msg) in pickle.load(open(rp, 'rb')).items():
        r = label.split('#')[0]
        agda[r][st == 'fail'] += 1
        if st == 'fail':
            fails[r].append(n)
syntax = defaultdict(lambda: [0, 0])
for p in glob.glob(f'{S}/c/*/steps.pkl.syntax'):
    for r, c in pickle.load(open(p, 'rb')).items():
        syntax[r][0] += c[True]
        syntax[r][1] += c[False]
used = set()
for p in glob.glob(f'{S}/c/*/rules-used'):
    used |= set(open(p).read().split())
ok_agda = {r for r, (p, f) in agda.items() if p and not f}
ok_syn = {r for r, (p, f) in syntax.items() if p and not f}
bad = {r for r, (p, f) in agda.items() if f} | {r for r, (p, f) in syntax.items() if f}
macro = {r for r in core if r.startswith('def.')}
print(f'core rules: {len(core)}; used by some script: {len(core & used)}')
print(f'validated in Agda: {len(core & ok_agda)}; by syntax reference: {len(core & ok_syn)}; '
      f'macros (def.*): {len(core & macro)}')
print(f'disagreeing: {len(core & bad)} core, {len(bad - core)} generated')
for r in sorted(bad):
    print(f'  {r}: agda pass/fail {agda[r]}, syntax {syntax[r]}, in {sorted(set(fails[r]))}')
rest = (core & used) - ok_agda - ok_syn - bad - macro
print(f'used but not validated ({len(rest)}):', ' '.join(sorted(rest)))
gen_ok = {r for r in ok_agda if generated(r)}
print(f'generated rules validated in Agda: {len(gen_ok)}')
