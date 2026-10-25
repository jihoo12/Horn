"""De Bruijn operations on Horn cubical terms, written independently of the theory's rules.

Term variables (v n) are bound by pi, sigma, lam and the motives of natrec and bif.
Dimension variables (dim n, at0 n, at1 n) are bound by path's type, plam, and comp's
type and system.
"""


def num(k):
    t = 'z'
    for _ in range(k):
        t = ('s', t)
    return t


def nat(n):
    k = 0
    while n != 'z':
        n, k = n[1], k + 1
    return k


# For each constructor: per argument, (term binders, dim binders) it adds.
BINDERS = {
    'pi': [(0, 0), (1, 0)], 'sigma': [(0, 0), (1, 0)], 'lam': [(1, 0)],
    'natrec': [(1, 0), (0, 0), (0, 0), (0, 0)], 'bif': [(1, 0), (0, 0), (0, 0), (0, 0)],
    'path': [(0, 1), (0, 0), (0, 0)], 'plam': [(0, 1)],
    'comp': [(0, 1), (0, 0), (0, 1), (0, 0)],
}


def walk(t, var, dim, tk=0, dk=0):
    """Rebuild t, replacing (v n) by var(n, tk, dk) and dimension indices by dim(n, tk, dk)
    (returning an I term for 'dim', or an index/face for at0/at1)."""
    if isinstance(t, str):
        return t
    h = t[0]
    if h == 'v':
        return var(nat(t[1]), tk, dk)
    if h == 'dim':
        return dim('dim', nat(t[1]), tk, dk)
    if h in ('at0', 'at1'):
        return dim(h, nat(t[1]), tk, dk)
    bs = BINDERS.get(h)
    out = [h]
    for n, a in enumerate(t[1:]):
        bt, bd = bs[n] if bs else (0, 0)
        out.append(walk(a, var, dim, tk + bt, dk + bd))
    return tuple(out)


def shift(t, by=1, cut=0):
    """Weaken term variables >= cut (counted under binders)."""
    def var(n, tk, dk):
        return ('v', num(n + by if n >= cut + tk else n))
    return walk(t, var, lambda h, n, tk, dk: (h, num(n)) if h != 'dim' else ('dim', num(n)))


def dshift(t, by=1, cut=0):
    def dim(h, n, tk, dk):
        return (h, num(n + by if n >= cut + dk else n))
    return walk(t, lambda n, tk, dk: ('v', num(n)), dim)


def subst(t, r):
    """Replace term variable 0 by r, lowering the others."""
    def var(n, tk, dk):
        if n < tk:
            return ('v', num(n))
        if n == tk:
            return dshift(shift(r, tk), dk)
        return ('v', num(n - 1))
    return walk(t, var, lambda h, n, tk, dk: (h, num(n)))


def ishift(r, by):
    if isinstance(r, str):
        return r
    if r[0] == 'dim':
        return ('dim', num(nat(r[1]) + by))
    return (r[0],) + tuple(ishift(x, by) for x in r[1:])


def face_of(h, r):
    """The face (r = 0) or (r = 1) for an interval term r."""
    one = h == 'at1'
    if r == 'i0':
        return 'ft' if not one else 'ff'
    if r == 'i1':
        return 'ft' if one else 'ff'
    k = r[0]
    if k == 'dim':
        return (h, r[1])
    if k == 'neg':
        return face_of('at0' if one else 'at1', r[1])
    if k in ('meet', 'join'):
        conj = (k == 'meet') == one
        return ('fand' if conj else 'for', face_of(h, r[1]), face_of(h, r[2]))
    raise ValueError(k)


def dsubst(t, r):
    """Replace dimension 0 by the interval term r, lowering the others."""
    def dim(h, n, tk, dk):
        if n < dk:
            return (h, num(n))
        if n == dk:
            rr = ishift(r, dk)
            return rr if h == 'dim' else face_of(h, rr)
        return (h, num(n - 1))
    return walk(t, lambda n, tk, dk: ('v', num(n)), dim)


def reduce_heads(t):
    """Contract redexes whose head Agda could not infer: (lam b) a, fst/snd (pair a b),
    (plam t) @ r, and ann around them."""
    if isinstance(t, str):
        return t
    t = (t[0],) + tuple(reduce_heads(x) for x in t[1:])
    h = t[0]
    if h == 'app' and not isinstance(t[1], str) and t[1][0] == 'lam':
        return reduce_heads(subst(t[1][1], t[2]))
    if h in ('fst', 'snd') and not isinstance(t[1], str) and t[1][0] == 'pair':
        return t[1][1] if h == 'fst' else t[1][2]
    if h == 'papp' and not isinstance(t[1], str) and t[1][0] == 'plam':
        return reduce_heads(dsubst(t[1][1], t[2]))
    return t
