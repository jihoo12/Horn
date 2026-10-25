"""Write Agda modules checking Horn judgments (untrusted research driver).

emit.py THEORY STEPS.pkl OUTDIR MODE [ARGS]
  MODE goals GOALS        the certificate's goals
  MODE rules K            up to K smallest rhas/req conclusions per rule
"""
import sys, os, pickle, random
from collections import defaultdict
sys.path.insert(0, os.path.dirname(__file__))
from expand import parse_all
from horn_syntax import reduce_heads
import datatypes
from to_agda import judgment, term, Env, Untranslatable, DEFS

HEADER = '{-# OPTIONS --cubical #-}\nmodule %s where\nopen import HornPrelude\n\n'


def defs_block(theory):
    """Agda definitions for the def/ constants, from their closed typing premises."""
    forms = parse_all(open(theory).read())
    datatypes.load(forms)
    out = [datatypes.agda_block(term, Env)]
    for f in forms:
        if f[0] == 'rule' and f[1].startswith('rhas.def/'):
            body, ty = reduce_heads(f[2][1][4]), reduce_heads(f[2][1][5])
            n = 'def-' + f[1][len('rhas.def/'):]
            DEFS['def/' + n[4:]] = (body, ty)
            out.append(f'{n} : {term(ty, Env())}\n{n} = {term(body, Env())}\n')
    return '\n'.join(out)


def size(t):
    return 1 if isinstance(t, str) else 1 + sum(size(x) for x in t)


def main():
    theory, pkl, outdir, mode = sys.argv[1:5]
    steps, used = pickle.load(open(pkl, 'rb'))
    os.makedirs(outdir, exist_ok=True)
    defs = defs_block(theory)
    items = []  # (label, judgment)
    if mode == 'goals':
        for g in parse_all(open(sys.argv[5]).read()):
            items.append((g[1], g[2]))
    else:
        k = int(sys.argv[5])
        by_rule = defaultdict(dict)
        for j, r in zip(steps, used):
            if j[0] in ('rhas', 'req'):
                by_rule[r].setdefault(j, None)
        for r, js in sorted(by_rule.items()):
            for n, j in enumerate(sorted(js, key=size)[:k]):
                items.append((f'{r}#{n}', j))
    open(os.path.join(outdir, 'HornDefs.agda'), 'w').write(
        HEADER % 'HornDefs' + defs)
    index, skipped = [], defaultdict(int)
    for n, (label, j) in enumerate(items):
        try:
            decls = judgment(j, f'j{n}')
        except (Untranslatable, AssertionError, IndexError, ValueError) as ex:
            skipped[str(ex)] += 1
            index.append((n, label, None, str(ex)))
            continue
        index.append((n, label, '\n'.join(decls), None))
    pickle.dump(index, open(os.path.join(outdir, 'items.pkl'), 'wb'))
    print(len(items), 'judgments;', sum(1 for x in index if x[2]), 'emitted;', dict(skipped))


if __name__ == '__main__':
    main()
