"""Expand a compact Horn certificate into ground judgments (untrusted)."""
import sys, re, pickle
sys.setrecursionlimit(100000)
TOK = re.compile(r'\(|\)|[^\s()]+')

def parse_all(text):
    toks = TOK.findall(re.sub(r';[^\n]*', '', text))
    out, stack = [], [[]]
    for t in toks:
        if t == '(':
            stack.append([])
        elif t == ')':
            x = tuple(stack.pop()); stack[-1].append(x)
        else:
            stack[-1].append(t)
    return stack[0]

def read_theory(path):
    rules = {}
    for f in parse_all(open(path).read()):
        if f[0] == 'rule':
            rules[f[1]] = (list(f[2]), f[3])
    return rules

def match(p, g, env):
    if isinstance(p, str):
        if p.startswith('?'):
            if p in env:
                return env[p] == g
            env[p] = g; return True
        return p == g
    if isinstance(g, str) or len(p) != len(g):
        return False
    return all(match(a, b, env) for a, b in zip(p, g))

def inst(p, env):
    if isinstance(p, str):
        return env[p] if p.startswith('?') else p
    return tuple(inst(a, env) for a in p)

def expand_defs(t, defs):
    if isinstance(t, str):
        return defs.get(t, t) if t.startswith('?') else t
    return tuple(expand_defs(a, defs) for a in t)

def expand(theory, proof):
    rules = read_theory(theory)
    defs, steps, used = {}, [], []
    for f in parse_all(open(proof).read()):
        if f[0] == 'def':
            defs[f[1]] = expand_defs(f[2], defs)
        elif f[0] == 'step':
            prem, concl = rules[f[2]]
            env = {}
            for p, i in zip(prem, f[3]):
                assert match(p, steps[int(i)], env), (f[1], f[2])
            stated = None
            for item in f[4:]:
                item = expand_defs(item, defs)
                if isinstance(item[0], str) and item[0].startswith('?') and len(item) == 2:
                    env[item[0]] = item[1]
                else:
                    stated = item
            if stated is not None:
                assert match(concl, stated, env)
            steps.append(inst(concl, env)); used.append(f[2])
    return steps, used

if __name__ == '__main__':
    steps, used = expand(sys.argv[1], sys.argv[2])
    pickle.dump((steps, used), open(sys.argv[3], 'wb'))
    from collections import Counter
    print(len(steps), Counter(s[0] for s in steps).most_common())
