"""Agda data types and eliminators for a theory's `data` declarations (untrusted).

Everything is read from the generated rules: parameters from `ty/X`, fields from
`rhas.ctor/X/c`, path endpoints from `req.ctor/X/c-0/1`.  Each data type becomes an
Agda (higher) inductive type, and `elim/X` a dependent eliminator by pattern matching
whose methods take the fields, then one hypothesis per recursive field, then (for a
path constructor) the interval, as in docs/CUBICAL_SCRIPT.md.
"""
import horn_syntax
from horn_syntax import num

DATA = {}  # X -> {'params': n, 'ctors': [(c, fields, ndims, ends)]}


def ident(s):
    return s.replace('/', '-')


def load(forms):
    sig = {f[1]: f[2] for f in forms if f[0] == 'ctor'}
    rules = {f[1]: f for f in forms if f[0] == 'rule'}
    for name, args in sig.items():
        if name.startswith('ty/'):
            DATA[name[3:]] = {'params': len(args), 'ctors': []}
    for name, args in sig.items():
        if not name.startswith('ctor/'):
            continue
        x = name.split('/')[1]
        concl = rules['rhas.' + name][3]
        metas = [a for a in (concl[4][1:] if isinstance(concl[4], tuple) else ())]
        fields = []
        for p in rules['rhas.' + name][2]:
            if p[0] == 'rhas' and p[4] in metas:
                fields.append((p[4], p[5]))
        ndims = sum(1 for a in args if a == 'I')
        ends = None
        if ndims:
            ends = [rules[f'req.{name}-{k}'][3][5] for k in (0, 1)]
        DATA[x]['ctors'].append((name, fields, ndims, ends))
    for x, d in DATA.items():
        n = d['params']
        horn_syntax.BINDERS['elim/' + x] = [(0, 0)] * n + [(1, 0)] + [(0, 0)] * (len(d['ctors']) + 1)


def recursive(ty, x):
    return ty == 'ty/' + x or (isinstance(ty, tuple) and ty[0] == 'ty/' + x)


def agda_block(term, Env):
    """Agda source for every declared data type, given the term translator."""
    out = []
    for x, d in DATA.items():
        n = d['params']
        ps = [f'A{k}' for k in range(n)]
        pmeta = {f'?A{k}': k for k in range(n)}
        head = f'ty-{ident(x)}' + ''.join(' ' + p for p in ps)

        def tr(t, scope):
            """Translate a rule-level term whose metas are the named variables in scope."""
            def go(t):
                if isinstance(t, str):
                    if t in scope:
                        return ('v', num(len(scope) - 1 - scope.index(t)))
                    return t
                return tuple(go(a) for a in t)
            e = Env()
            for _ in scope:
                e, _ = e.with_var()
            e.vars = [s.lstrip('?') for s in scope]
            return term(go(t), e)

        params = [f'?A{k}' for k in range(n)]
        lines = [f'data ty-{ident(x)}' + ''.join(f' ({p} : Set)' for p in ps) + ' : Set where']
        for c, fields, ndims, ends in sorted(d['ctors'], key=lambda c: c[2]):
            scope = list(params)
            tel = []
            for m, ty in fields:
                tel.append(f'({m[1:]} : {tr(ty, scope)})')
                scope.append(m)
            res = head
            if ndims:
                res = f'PathP (λ _ → {head}) {tr(ends[0], scope)} {tr(ends[1], scope)}'
            lines.append(f'  {ident(c)} : ' + ' → '.join(tel + [res]))
        out.append('\n'.join(lines) + '\n')

        # Eliminator.
        ctors = d['ctors']
        ms = [f'm{k}' for k in range(len(ctors))]

        def spell(t, scope, ihs):
            """The eliminator's value on an endpoint, through methods and hypotheses."""
            if isinstance(t, str) and t in ihs:
                return ihs[t]
            c = t if isinstance(t, str) else t[0]
            k = [cc[0] for cc in ctors].index(c)
            _, fields, ndims, _ = ctors[k]
            args = [] if isinstance(t, str) else list(t[1:])
            parts = [tr(a, scope) for a in args[:len(fields)]]
            for (m, ty), a in zip(fields, args):
                if recursive(ty, x):
                    parts.append(spell(a, scope, ihs))
            return '(' + ' '.join([ms[k]] + parts) + ')'

        mtypes = []
        for k, (c, fields, ndims, ends) in enumerate(ctors):
            scope = list(params)
            tel, ihs, ih_tel = [], {}, []
            for m, ty in fields:
                tel.append(f'({m[1:]} : {tr(ty, scope)})')
                scope.append(m)
            for m, ty in fields:
                if recursive(ty, x):
                    ihs[m] = f'h{m[1:]}'
                    ih_tel.append(f'(h{m[1:]} : P {m[1:]})')
            fs = ' '.join(m[1:] for m, _ in fields)
            if ndims:
                res = (f'PathP (λ i → P ({ident(c)} {fs} i)) '
                       f'{spell(ends[0], scope, ihs)} {spell(ends[1], scope, ihs)}')
            else:
                res = f'P ({ident(c)} {fs})' if fs else f'P {ident(c)}'
            mtypes.append(' → '.join(tel + ih_tel + [res]))
        e = f'elim-{ident(x)}'
        sig = (f'{e} : ∀ {{ℓ}}' + ''.join(f' ({p} : Set)' for p in ps) +
               f' (P : {head} → Set ℓ)' + ''.join(f' ({m} : {t})' for m, t in zip(ms, mtypes)) +
               f' (x : {head}) → P x')
        clauses = [sig]
        call = ' '.join([e] + ps + ['P'] + ms)
        for k, (c, fields, ndims, ends) in enumerate(ctors):
            fs = [m[1:] for m, _ in fields]
            ih = [f'({call} {m[1:]})' for m, ty in fields if recursive(ty, x)]
            pat = ' '.join([ident(c)] + fs + (['i'] if ndims else []))
            rhs = ' '.join([ms[k]] + fs + ih + (['i'] if ndims else []))
            clauses.append(f'{call} ({pat}) = {rhs}' if fs or ndims else f'{call} {ident(c)} = {rhs}')
        out.append('\n'.join(clauses) + '\n')
    return '\n'.join(out)
