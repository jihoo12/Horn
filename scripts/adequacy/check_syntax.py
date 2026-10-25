"""Check every syntactic fact of an expanded certificate against reference semantics
written independently of the theory's rules (untrusted research tool).

check_syntax.py STEPS.pkl [THEORY]
"""
import sys, os, pickle, itertools
from collections import Counter, defaultdict
sys.path.insert(0, os.path.dirname(__file__))
import horn_syntax
from horn_syntax import walk, num, nat, face_of


def shift(t, k):
    return walk(t, lambda n, tk, dk: ('v', num(n + 1 if n >= k + tk else n)),
                lambda h, n, tk, dk: (h, num(n)))


def dshift(t, k):
    return walk(t, lambda n, tk, dk: ('v', num(n)),
                lambda h, n, tk, dk: (h, num(n + 1 if n >= k + dk else n)))


def dshift_by(t, by):
    for _ in range(by):
        t = dshift(t, 0)
    return t


def shift_by(t, by):
    for _ in range(by):
        t = shift(t, 0)
    return t


def subst(t, k, r):
    def var(n, tk, dk):
        if n < k + tk:
            return ('v', num(n))
        if n == k + tk:
            return dshift_by(shift_by(r, tk), dk)
        return ('v', num(n - 1))
    return walk(t, var, lambda h, n, tk, dk: (h, num(n)))


def dsubst(t, k, r):
    def dim(h, n, tk, dk):
        if n < k + dk:
            return (h, num(n))
        if n == k + dk:
            rr = dshift_by(r, dk)
            return rr if h == 'dim' else face_of(h, rr)
        return (h, num(n - 1))
    return walk(t, lambda n, tk, dk: ('v', num(n)), dim)


# --- faces: the free distributive lattice on (i=0), (i=1) with (i=0)∧(i=1) = 0 ---

def clauses(f):
    if f == 'ft':
        return [frozenset()]
    if f == 'ff':
        return []
    h = f[0]
    if h in ('at0', 'at1'):
        return [frozenset([(nat(f[1]), h == 'at1')])]
    if h == 'for':
        return clauses(f[1]) + clauses(f[2])
    if h == 'fand':
        out = []
        for a in clauses(f[1]):
            for b in clauses(f[2]):
                c = a | b
                if not any((i, not v) in c for i, v in c):
                    out.append(c)
        return out
    raise ValueError(h)


def leq(f, g):
    gs = clauses(g)
    return all(any(c2 <= c for c2 in gs) for c in clauses(f))


# --- intervals: the free de Morgan algebra, decided in the 4-element generator ---

ORDER = {(0, 0), (0, 'a'), (0, 'b'), (0, 1), ('a', 'a'), ('a', 1), ('b', 'b'), ('b', 1), (1, 1)}


def meet(x, y):
    if (x, y) in ORDER:
        return x
    if (y, x) in ORDER:
        return y
    return 0


def join(x, y):
    if (x, y) in ORDER:
        return y
    if (y, x) in ORDER:
        return x
    return 1


def ev(r, rho):
    if r == 'i0':
        return 0
    if r == 'i1':
        return 1
    h = r[0]
    if h == 'dim':
        return rho[nat(r[1])]
    if h == 'neg':
        x = ev(r[1], rho)
        return {0: 1, 1: 0}.get(x, x)
    if h == 'meet':
        return meet(ev(r[1], rho), ev(r[2], rho))
    if h == 'join':
        return join(ev(r[1], rho), ev(r[2], rho))
    raise ValueError(h)


def dims_of(t, acc=None):
    acc = set() if acc is None else acc
    if isinstance(t, tuple):
        if t[0] in ('dim', 'at0', 'at1'):
            acc.add(nat(t[1]))
        else:
            for a in t[1:]:
                dims_of(a, acc)
    return acc


def interval_eq_under(phi, r, s):
    """r = s in the free de Morgan algebra, under every clause of phi."""
    ds = sorted(dims_of(r) | dims_of(s) | dims_of(phi))
    for c in clauses(phi):
        fixed = {i: (1 if v else 0) for i, v in c}
        free = [d for d in ds if d not in fixed]
        for vals in itertools.product((0, 1, 'a', 'b'), repeat=len(free)):
            rho = defaultdict(lambda: 0, fixed)
            rho.update(zip(free, vals))
            if ev(r, rho) != ev(s, rho):
                return False
    return True


def free_ok(t, n, d):
    """All term variables < n and dimensions < d (counting binders)."""
    bad = []
    walk(t, lambda k, tk, dk: bad.append(1) if k >= n + tk else ('v', num(k)),
         lambda h, k, tk, dk: bad.append(1) if k >= d + dk else (h, num(k)))
    return not bad


def ctx_list(g):
    out = []
    while g != 'nil':
        out.append(g[1]); g = g[2]
    return out


def check(j):
    """True/False for facts with a reference meaning, None for others."""
    h = j[0]
    if h in ('shift', 'sshift'):
        return shift(j[1], nat(j[2])) == j[3]
    if h in ('dshift', 'sdshift', 'fshift', 'ishift'):
        return dshift(j[1], nat(j[2])) == j[3]
    if h in ('subst', 'ssubst'):
        return subst(j[1], nat(j[2]), j[3]) == j[4]
    if h in ('dsubst', 'sdsubst', 'fsubst', 'isubst'):
        return dsubst(j[1], nat(j[2]), j[3]) == j[4]
    if h == 'dshiftctx':
        a, b = ctx_list(j[1]), ctx_list(j[3])
        return len(a) == len(b) and all(dshift(x, nat(j[2])) == y for x, y in zip(a, b))
    if h == 'lookup':
        g = ctx_list(j[1]); n = nat(j[2])
        return n < len(g) and shift_by(g[n], n + 1) == j[3]
    if h == 'length':
        return len(ctx_list(j[1])) == nat(j[2])
    if h == 'le':
        return nat(j[1]) <= nat(j[2])
    if h == 'lt':
        return nat(j[1]) < nat(j[2])
    if h == 'max':
        return max(nat(j[1]), nat(j[2])) == nat(j[3])
    if h == 'scoped':
        return free_ok(j[3], nat(j[2]), nat(j[1]))
    if h == 'sscoped':
        return free_ok(j[3], nat(j[2]), nat(j[1]))
    if h in ('interval', 'face'):
        return free_ok(j[2], 0, nat(j[1]))
    if h == 'entails':
        return free_ok(j[2], 0, nat(j[1])) and leq(j[2], j[3])
    if h == 'boundary':
        f0, f1 = face_of('at0', j[1]), face_of('at1', j[1])
        return leq(f0, j[2]) and leq(j[2], f0) and leq(f1, j[3]) and leq(j[3], f1)
    if h == 'local':
        return interval_eq_under(j[2], j[3], j[4])
    if h == 'ieq':
        return interval_eq_under('ft', j[1], j[2])
    if h == 'member':
        return j[1] in flist(j[2])
    if h == 'take':
        xs, ys = flist(j[1]), flist(j[3])
        return j[2] in xs and any(xs[:i] + xs[i + 1:] == ys for i, x in enumerate(xs) if x == j[2])
    if h == 'cover':
        hyp = 'ft'
        for f in flist(j[1]):
            hyp = ('fand', hyp, f)
        return leq(hyp, j[2])
    if h == 'branch':
        s = j[1]
        while s != 'snil':
            if (s[1], s[2]) == (j[2], j[3]):
                return True
            s = s[3]
        return False
    if h == 'fforall':
        k = nat(j[2])
        keep = 'ff'
        for c in clauses(j[1]):
            if all(i != k for i, _ in c):
                f = 'ft'
                for i, v in c:
                    f = ('fand', f, ('at1' if v else 'at0', num(i - 1 if i > k else i)))
                keep = ('for', keep, f)
        return leq(keep, j[3]) and leq(j[3], keep)
    return None


def flist(fs):
    out = []
    while fs != 'fnil':
        out.append(fs[1]); fs = fs[2]
    return out


def main():
    if len(sys.argv) > 2:  # binders of the theory's eliminators
        import datatypes
        from expand import parse_all
        datatypes.load(parse_all(open(sys.argv[2]).read()))
    steps, used = pickle.load(open(sys.argv[1], 'rb'))
    res = defaultdict(Counter)
    bad = defaultdict(list)
    seen = set()
    for j, r in zip(steps, used):
        if j in seen:
            continue
        seen.add(j)
        try:
            v = check(j)
        except (ValueError, KeyError, IndexError, TypeError) as ex:
            v = 'error'
        res[r][v] += 1
        if v is False or v == 'error':
            bad[r].append(j)
    ok = sum(c[True] for c in res.values())
    no = sum(c[False] for c in res.values())
    print(f'{ok} facts agree, {no} disagree, '
          f'{sum(c["error"] for c in res.values())} errors, '
          f'{sum(c[None] for c in res.values())} without a reference meaning')
    print('rules checked:', sum(1 for c in res.values() if c[True] and not c[False]),
          ' disagreeing:', sorted(bad))
    for r, js in sorted(bad.items()):
        print(' ', r, str(js[0])[:300])
    unchecked = sorted(r for r, c in res.items() if c[None])
    print('no reference meaning:', ' '.join(unchecked))
    pickle.dump(dict(res), open(sys.argv[1] + '.syntax', 'wb'))


if __name__ == '__main__':
    main()
