"""Translate Horn cubical judgments into Cubical Agda (untrusted research tool).

rhas d G psi t A    ~>  for each DNF clause of psi:  (dims) (G) -> A  :=  t
req  d G psi t u A  ~>  for each DNF clause of psi:  (dims) (G) -> PathP (λ _ -> A) t u  :=  λ _ -> t
Agda accepts the second only if t and u are definitionally equal in Cubical Agda.
"""
from horn_syntax import reduce_heads, shift, dshift, subst, dsubst
from datatypes import DATA, ident


class Untranslatable(Exception):
    pass


def nat(n):
    k = 0
    while n != 'z':
        assert n[0] == 's', n
        n, k = n[1], k + 1
    return k


def level(n):
    k = nat(n)
    return 'lzero' if k == 0 else '(' + 'lsuc (' * k + 'lzero' + ')' * k + ')'


class Env:
    """dims: list of Agda expressions ('iN', 'i0', 'i1'), innermost last; vars: names."""

    def __init__(self, dims=(), vars=(), fresh=None, tys=()):
        self.dims, self.vars = list(dims), list(vars)
        self.fresh = fresh if fresh is not None else [0]
        # Horn type of each variable (or None) and the dimension count where it was bound.
        self.tys = list(tys) or [(None, 0)] * len(self.vars)

    def name(self, prefix):
        self.fresh[0] += 1
        return f'{prefix}{self.fresh[0]}'

    def with_dim(self, value=None):
        e = Env(self.dims, self.vars, self.fresh, self.tys)
        n = value or self.name('r')
        e.dims.append(n)
        return e, n

    def with_var(self, ty=None):
        e = Env(self.dims, self.vars, self.fresh, self.tys)
        n = self.name('x')
        e.vars.append(n)
        e.tys.append((ty, len(self.dims)))
        return e, n

    def type_of(self, k):
        ty, nd = self.tys[-1 - k]
        if ty is None:
            return None
        return dshift(shift(ty, k + 1), len(self.dims) - nd)

    def restrict(self, clause):
        return Env([('i1' if clause[d] else 'i0') if d in clause else d for d in self.dims],
                   self.vars, self.fresh, self.tys)


def dim(env, n):
    k = nat(n)
    if k >= len(env.dims):
        raise Untranslatable('free dimension')
    return env.dims[-1 - k]


def interval(r, env):
    if r in ('i0', 'i1'):
        return r
    h = r[0]
    if h == 'dim':
        return dim(env, r[1])
    if h == 'neg':
        return f'(~ {interval(r[1], env)})'
    if h in ('meet', 'join'):
        op = '∧' if h == 'meet' else '∨'
        return f'({interval(r[1], env)} {op} {interval(r[2], env)})'
    raise Untranslatable(f'interval {h}')


def dnf(f, env):
    """Clauses (dict dim-name -> 0/1) whose disjunction is the face f."""
    if f == 'ft':
        return [{}]
    if f == 'ff':
        return []
    h = f[0]
    if h in ('at0', 'at1'):
        d = dim(env, f[1])
        want = 0 if h == 'at0' else 1
        if d in ('i0', 'i1'):
            return [{}] if (d == 'i1') == bool(want) else []
        return [{d: want}]
    if h == 'for':
        out = dnf(f[1], env)
        for c in dnf(f[2], env):
            if c not in out:
                out.append(c)
        return out
    if h == 'fand':
        out = []
        for a in dnf(f[1], env):
            for b in dnf(f[2], env):
                if all(a[k] == b[k] for k in a.keys() & b.keys()):
                    c = {**a, **b}
                    if c not in out:
                        out.append(c)
        return out
    raise Untranslatable(f'face {h}')


def face(f, env):
    cs = dnf(f, env)
    if not cs:
        return 'i0'
    if {} in cs:
        return 'i1'
    return '(' + ' ∨ '.join('(' + ' ∧ '.join(d if v else f'(~ {d})' for d, v in c.items()) + ')'
                            for c in cs) + ')'


def partial(f, t, env, tr=None, tenv=None):
    """A partial element of face f (read in env); t is read in tenv under each clause."""
    tr = tr or term
    tenv = tenv or env
    cs = dnf(f, env)
    if not cs:
        return 'isOneEmpty'
    if {} in cs:
        return f'(λ _ → {tr(t, tenv)})'
    arms = []
    for c in cs:
        pats = ' '.join(f'({d} = {"i1" if v else "i0"})' for d, v in c.items())
        arms.append(f'{pats} → {tr(t, tenv.restrict(c))}')
    return '(λ { ' + ' ; '.join(arms) + ' })'


def side(s, env):
    """The Horn term of the first side of a system whose face holds here."""
    while s != 'snil':
        _, f, t, rest = s
        if {} in dnf(f, env):
            return t
        s = rest
    raise Untranslatable('system with no true side')


def system(s, env):
    return term(side(s, env), env)


def resolve(t, env):
    """t with systems selected and head redexes contracted, at the Horn level."""
    while not isinstance(t, str) and t[0] == 'system':
        t = side(t[1], env)
    if isinstance(t, str) or t[0] not in ('app', 'papp', 'fst', 'snd'):
        return t
    f = resolve(t[1], env)
    if isinstance(f, str):
        return t
    if t[0] == 'app' and f[0] == 'lam':
        return resolve(reduce_heads(subst(f[1], t[2])), env)
    if t[0] == 'papp' and f[0] == 'plam':
        return resolve(reduce_heads(dsubst(f[1], t[2])), env)
    if t[0] in ('fst', 'snd') and f[0] == 'pair':
        return resolve(f[1] if t[0] == 'fst' else f[2], env)
    return t


def term(t, env):
    t = resolve(t, env)
    if isinstance(t, str):
        simple = {'nat': 'ℕ', 'zero': 'zero', 'bool': '𝔹', 'btrue': 'true',
                  'bfalse': 'false', 's1': 'S¹', 'base': 'base'}
        if t in simple:
            return simple[t]
        if t.startswith('def/'):
            return 'def-' + t[4:]
        if t.startswith('ty/') or t.startswith('ctor/'):
            return ident(t)
        raise Untranslatable(f'atom {t}')
    h = t[0]
    if h == 'u':
        return f'(Set {level(t[1])})'
    if h == 'v':
        k = nat(t[1])
        if k >= len(env.vars):
            raise Untranslatable('free variable')
        return env.vars[-1 - k]
    if h in ('pi', 'sigma'):
        a = term(t[1], env)
        e, x = env.with_var(t[1])
        b = term(t[2], e)
        return f'(({x} : {a}) → {b})' if h == 'pi' else f'(Σ {a} (λ {x} → {b}))'
    if h == 'lam':
        e, x = env.with_var()
        return f'(λ {x} → {term(t[1], e)})'
    if h == 'app':
        return f'({term(t[1], env)} {term(t[2], env)})'
    if h == 'path':
        e, i = env.with_dim()
        return f'(PathP (λ {i} → {term(t[1], e)}) {term(t[2], env)} {term(t[3], env)})'
    if h == 'plam':
        e, i = env.with_dim()
        return f'(λ {i} → {term(t[1], e)})'
    if h == 'papp':
        return f'({term(t[1], env)} {interval(t[2], env)})'
    if h == 'comp':
        _, a, phi, u, b = t
        e, i = env.with_dim()
        if TRANSP_FF and not dnf(phi, env):
            return f'(transpC (λ {i} → {term(a, e)}) {term(b, env)})'
        # phi lives outside the binder; read it in e, where it was shifted.
        return (f'(compC (λ {i} → {term(a, e)}) {{{face(phi, env)}}} '
                f'(λ {i} → {partial(phi, u, env, tenv=e)}) (inS {term(b, env)}))')
    if h == 'system':
        return system(t[1], env)
    if h == 'pair':
        return f'({term(t[1], env)} , {term(t[2], env)})'
    if h in ('fst', 'snd', 'suc'):
        return f'({h} {term(t[1], env)})'
    if h in ('natrec', 'bif'):
        e, x = env.with_var('nat' if h == 'natrec' else 'bool')
        return f'({h} (λ {x} → {term(t[1], e)}) {term(t[2], env)} {term(t[3], env)} {term(t[4], env)})'
    if h == 'loop':
        return f'(loop {interval(t[1], env)})'
    if h == 's1rec':
        return f'(s1rec {" ".join(term(x, env) for x in t[1:])})'
    if h == 'ann':
        return f'(ann {term(t[2], env)} {term(t[1], env)})'
    if h == 'glue-type':
        _, a, phi, ty, eq = t
        return (f'(GlueC {term(a, env)} {{{face(phi, env)}}} {partial(phi, ty, env)} '
                f'{partial(phi, eq, env, lambda x, e: "(mkEquiv " + term(x, e) + ")")})')
    if h == 'glue':
        _, g, u, v = t
        if g[0] != 'glue-type':
            raise Untranslatable('glue without its type')
        _, a, phi, ty, eq = g
        return (f'(glueC {{A = {term(a, env)}}} {{φ = {face(phi, env)}}} '
                f'{{T = {partial(phi, ty, env)}}} '
                f'{{e = {partial(phi, eq, env, lambda x, e: "(mkEquiv " + term(x, e) + ")")}}} '
                f'{partial(phi, u, env)} (inS {term(v, env)}))')
    if h == 'unglue':
        g = whnf(synth(t[1], env))
        if g is None or isinstance(g, str) or g[0] != 'glue-type':
            return f'(prim^unglue {term(t[1], env)})'
        _, a, phi, ty, eq = g
        return (f'(prim^unglue {{A = {term(a, env)}}} {{φ = {face(phi, env)}}} '
                f'{{T = {partial(phi, ty, env)}}} '
                f'{{e = {partial(phi, eq, env, lambda x, e: "(mkEquiv " + term(x, e) + ")")}}} '
                f'{term(t[1], env)})')
    if h.startswith('ty/'):
        return '(' + ' '.join([ident(h)] + [term(a, env) for a in t[1:]]) + ')'
    if h.startswith('ctor/'):
        x = h.split('/')[1]
        nd = next(c[2] for c in DATA[x]['ctors'] if c[0] == h)
        args = t[1:]
        tms, ivs = args[:len(args) - nd], args[len(args) - nd:]
        return '(' + ' '.join([ident(h)] + [term(a, env) for a in tms] +
                              [interval(r, env) for r in ivs]) + ')'
    if h.startswith('elim/'):
        n = DATA[h[5:]]['params']
        e, k = env.with_var(('ty/' + h[5:],) + t[1:1 + n] if n else 'ty/' + h[5:])
        parts = [term(a, env) for a in t[1:1 + n]] + [f'(λ {k} → {term(t[1 + n], e)})']
        parts += [term(a, env) for a in t[2 + n:]]
        return '(' + ' '.join(['elim-' + h[5:].replace('/', '-')] + parts) + ')'
    raise Untranslatable(f'term {h}')


import os
TRANSP_FF = os.environ.get('HORN_COMP_FF') == 'transp'
DEFS = {}  # def/ constant -> (body, type)


def whnf(t):
    """Weak head form of a type, enough to expose a Glue type: delta, beta, annotations."""
    for _ in range(200):
        if t is None or isinstance(t, str):
            if isinstance(t, str) and t in DEFS:
                t = DEFS[t][0]
                continue
            return t
        t = reduce_heads(t)
        h = t[0]
        if h in ('app', 'papp', 'fst', 'snd') and not isinstance(t[1], str) and t[1][0] == 'ann':
            t = (h, t[1][1]) + t[2:]
        elif h in ('app', 'papp', 'fst', 'snd'):
            f = whnf(t[1])
            if f == t[1] or f is None:
                return t
            t = (h, f) + t[2:]
        elif h == 'ann':
            t = t[1]
        else:
            return t
    return t


def synth(t, env):
    """The Horn type of t where it can be read off, else None."""
    if isinstance(t, str):
        return DEFS[t][1] if t in DEFS else None
    h = t[0]
    if h == 'v':
        k = nat(t[1])
        return env.type_of(k) if k < len(env.vars) else None
    if h == 'ann':
        return t[2]
    if h == 'comp':
        return dsubst(t[1], 'i1')
    if h == 'glue':
        return t[1]
    if h == 's1rec':
        return t[1]
    if h in ('natrec', 'bif'):
        return subst(t[1], t[4])
    if h.startswith('elim/'):
        n = DATA[h[5:]]['params']
        return subst(t[1 + n], t[-1])
    if h in ('app', 'papp', 'fst', 'snd', 'unglue'):
        f = whnf(synth(t[1], env))
        if f is None or isinstance(f, str):
            return None
        if h == 'app' and f[0] == 'pi':
            return subst(f[2], t[2])
        if h == 'papp' and f[0] == 'path':
            return dsubst(f[1], t[2])
        if h == 'fst' and f[0] == 'sigma':
            return f[1]
        if h == 'snd' and f[0] == 'sigma':
            return subst(f[2], ('fst', t[1]))
        if h == 'unglue' and f[0] == 'glue-type':
            return f[1]
    return None


def telescope(d, ctx, env):
    """Bind d dimensions then the context; returns (binders, lambda names, env)."""
    binders, names = [], []
    for _ in range(nat(d)):
        env, i = env.with_dim()
        binders.append(f'({i} : I)')
        names.append(i)
    types = []
    while ctx != 'nil':
        types.append(ctx[1])
        ctx = ctx[2]
    return binders, names, env, types[::-1]


def judgment(j, name):
    """Agda declarations for a ground rhas/req judgment, one per clause of its face."""
    j = reduce_heads(j)
    head = j[0]
    d, ctx, psi = j[1], j[2], j[3]
    out = []
    base = Env()
    binders, names, env, types = telescope(d, ctx, base)
    for k, clause in enumerate(dnf(psi, env)):
        e = env.restrict(clause)
        bs, ns = list(binders), list(names)
        ce = Env(e.dims, [], e.fresh)
        for ty in types:
            a = term(ty, ce)
            ce, x = ce.with_var(ty)
            bs.append(f'({x} : {a})')
            ns.append(x)
        if head == 'rhas':
            ty, body = term(j[5], ce), term(j[4], ce)
        else:
            t, u, a = term(j[4], ce), term(j[5], ce), term(j[6], ce)
            ty, body = f'PathP (λ _ → {a}) {t} {u}', f'λ _ → {t}'
        pi = ' → '.join(bs + [ty]) if bs else ty
        lam = f'λ {" ".join(ns)} → {body}' if ns else body
        out.append(f'{name}-{k} : {pi}\n{name}-{k} = {lam}\n')
    return out
