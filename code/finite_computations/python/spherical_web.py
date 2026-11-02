"""Exact normalized affine-Hecke evaluation of thin crossing diagrams.

This independent sparse Laurent implementation is intentionally small.  It
does not import the supplied KL code.  In the spherical right module the
standard vectors M_w have minimal LEFT finite-parabolic labels.  The local
bar-invariant crossing is b_s=H_s+v, where
  (H_s+v)(H_s-v**-1)=0,
and every finite H_s acts on M_e by v**-1.  Thus:
  M_w b_s = M_ws + v M_w             (ascent),
            M_ws + v**-1 M_w         (descent),
            (v+v**-1) M_w            (finite-parabolic wall).

The thick source is retained through the wall rule.  Canonicalization is
triangular, with leading coefficient one and lower coefficients in v Z[v].
These thin crossing calculations lift to affine q-webs through the cited
Schur equivalence; no unproved thick packet simplification is built in.
"""
from functools import lru_cache
from itertools import permutations, product


def plus(p, q, scale=1, shift=0):
    for degree, coefficient in q.items():
        degree += shift
        p[degree] = p.get(degree, 0) + scale * coefficient
        if not p[degree]:
            del p[degree]


def times(p, q):
    out = {}
    for degree, coefficient in p.items():
        plus(out, q, coefficient, degree)
    return out


def add_vector(out, vec, scalar=None, scale=1):
    scalar = {0: 1} if scalar is None else scalar
    for w, p in vec.items():
        target = out.setdefault(w, {})
        plus(target, times(scalar, p), scale)
        if not target:
            del out[w]


def json_poly(p):
    return {str(k): p[k] for k in sorted(p)}


def divide_laurent(p, q):
    """Return integral Laurent quotient/remainder for a monic divisor."""
    if not p:
        return {}, {}
    pmin, qmin = min(p), min(q)
    work = {k - pmin: c for k, c in p.items()}
    divisor = {k - qmin: c for k, c in q.items()}
    degree = max(divisor)
    quotient = {}
    while work and max(work) >= degree:
        d = max(work) - degree
        c, remainder = divmod(work[max(work)], divisor[degree])
        assert not remainder
        quotient[d + pmin - qmin] = c
        plus(work, divisor, scale=-c, shift=d)
    return quotient, {k + pmin: c for k, c in work.items()}


class SphericalWeb:
    def __init__(self, period):
        self.N = period
        self.identity = tuple(range(1, period + 1))
        self.canonical_cache = {self.identity: {self.identity: {0: 1}}}
        self.correction_cache = {}

    def value(self, w, i):
        period, residue = divmod(i - 1, self.N)
        return w[residue] + period * self.N

    @lru_cache(maxsize=None)
    def inverse(self, w):
        result = [0] * self.N
        for i, value in enumerate(w, 1):
            period, residue = divmod(value - 1, self.N)
            result[residue] = i - period * self.N
        return tuple(result)

    @lru_cache(maxsize=None)
    def right(self, w, s):
        if s:
            order = list(range(1, self.N + 1))
            order[s - 1], order[s] = order[s], order[s - 1]
        else:
            order = [0] + list(range(2, self.N)) + [self.N + 1]
        return tuple(self.value(w, i) for i in order)

    @lru_cache(maxsize=None)
    def length(self, w):
        return sum(abs((w[j] - w[i]) // self.N)
                   for i in range(self.N) for j in range(i + 1, self.N))

    @lru_cache(maxsize=None)
    def is_minimal(self, w):
        inv = self.inverse(w)
        return all(a < b for a, b in zip(inv, inv[1:]))

    def descent(self, w):
        length = self.length(w)
        return next(s for s in range(self.N)
                    if self.length(self.right(w, s)) == length - 1)

    def reduced_word(self, w):
        reverse = []
        while w != self.identity:
            s = self.descent(w)
            reverse.append(s)
            w = self.right(w, s)
        return list(reversed(reverse))

    def local_crossing(self, vector, s):
        out = {}
        for w, p in vector.items():
            ws = self.right(w, s)
            if self.is_minimal(ws):
                plus(out.setdefault(ws, {}), p)
                shift = 1 if self.length(ws) > self.length(w) else -1
                plus(out.setdefault(w, {}), p, shift=shift)
            else:
                plus(out.setdefault(w, {}), p, shift=1)
                plus(out.setdefault(w, {}), p, shift=-1)
        return {w: p for w, p in out.items() if p}

    def local_hecke(self, vector, s):
        """The normalized crossing H_s=b_s-v, including negative coefficients."""
        out = self.local_crossing(vector, s)
        add_vector(out, vector, {1: 1}, scale=-1)
        return out

    def evaluate(self, word, canonical_crossings=True):
        vec = {self.identity: {0: 1}}
        operation = self.local_crossing if canonical_crossings else self.local_hecke
        for s in word:
            vec = operation(vec, s)
        return vec

    def canonical(self, w):
        if w in self.canonical_cache:
            return self.canonical_cache[w]
        assert self.is_minimal(w)
        s = self.descent(w)
        parent = self.right(w, s)
        vec = self.local_crossing(self.canonical(parent), s)
        corrections = []
        # General triangular elimination makes no positivity assumption about
        # the intermediate expression. A negative coefficient a v^-d forces
        # the self-dual subtraction a(v^-d+v^d); constants are subtracted once.
        while True:
            bad = [y for y, p in vec.items()
                   if y != w and any(d <= 0 for d in p)]
            if not bad:
                break
            y = max(bad, key=lambda z: (self.length(z), z))
            scalar = {}
            for d, c in vec[y].items():
                if d < 0:
                    scalar[d] = c
                    scalar[-d] = c
                elif d == 0:
                    scalar[0] = c
            add_vector(vec, self.canonical(y), scalar, scale=-1)
            corrections.append((y, scalar))
        assert vec[w] == {0: 1}
        assert all(d > 0 and c >= 0 for y, p in vec.items() if y != w
                   for d, c in p.items())
        self.canonical_cache[w] = vec
        self.correction_cache[w] = (parent, s, corrections)
        return vec

    def canonical_expansion(self, vector):
        remaining = {w: dict(p) for w, p in vector.items()}
        answer = {}
        while remaining:
            w = max(remaining, key=lambda z: (self.length(z), z))
            scalar = dict(remaining[w])
            answer[w] = scalar
            add_vector(remaining, self.canonical(w), scalar, scale=-1)
        return answer

    def output_generators(self, m):
        return tuple(s for s in range(1, self.N) if s not in (m, m + 1))

    def finite_output_longest(self, m):
        return tuple(list(range(m, 0, -1)) + [m + 1]
                     + list(range(self.N, m + 1, -1)))

    def compose(self, w, z):
        return tuple(self.value(w, i) for i in z)

    def output_symmetrize(self, vector, m):
        """Multiply by C_{w_(m,1,m)}=sum_h v^(L-l(h)) H_h.

        This is the integral canonical finite-longest element, not an
        idempotent divided by a Poincare polynomial.
        """
        out = {}
        L = m * (m - 1)
        for first, last in product(permutations(range(1, m + 1)),
                                   permutations(range(m + 2, self.N + 1))):
            h = first + (m + 1,) + last
            vec = vector
            for s in self.reduced_word(h):
                vec = self.local_hecke(vec, s)
            add_vector(out, vec, {L - self.length(h): 1})
        return out

    def corner_raw(self, x, m):
        y = x
        while True:
            descents = [s for s in self.output_generators(m)
                        if self.is_minimal(self.right(y, s))
                        and self.length(self.right(y, s)) < self.length(y)]
            if not descents:
                break
            y = self.right(y, descents[0])
        word = self.reduced_word(y)
        raw = self.output_symmetrize(self.evaluate(word), m)
        self.check_output_symmetry(raw, m)
        return word, raw

    def check_output_symmetry(self, vector, m):
        for s in self.output_generators(m):
            defect = self.local_hecke(vector, s)
            add_vector(defect, vector, {-1: 1}, scale=-1)
            assert not defect, (m, s, defect)

    def orbit_maximum(self, w, m):
        while True:
            ascents = [self.right(w, s) for s in self.output_generators(m)
                       if self.is_minimal(self.right(w, s))
                       and self.length(self.right(w, s)) > self.length(w)]
            if not ascents:
                return w
            w = max(ascents)

    def corner_standard(self, vector, m):
        """Group spherical standards into normalized Schur standards.

        In an output-parabolic orbit, the maximal representative z gives
        coefficient 1 and the other representatives w coefficient
        v^(length(z)-length(w)). The eigenvector equations verify this.
        """
        self.check_output_symmetry(vector, m)
        out = {}
        for w in vector:
            z = self.orbit_maximum(w, m)
            out[z] = vector[z]
            expected = {}
            plus(expected, vector[z], shift=self.length(z) - self.length(w))
            assert expected == vector[w]
        return out

    def corner_matrix(self, maximal_label, m):
        u = self.inverse(maximal_label)
        rows = [range(1, m + 1), [m + 1], range(m + 2, self.N + 1)]
        matrix = [[sum(r in {x + t * self.N for x in u} for r in row)
                   for t in (-1, 0, 1)] for row in rows]
        assert [sum(row) for row in matrix] == [m, 1, m]
        return matrix


def family(m, j):
    N = 2 * m + 1
    negative = set(range(1, j)) | {m + 2}
    positive = {m} | set(range(N - j + 2, N + 1))
    u = tuple(sorted(i + N * (int(i in positive) - int(i in negative))
                     for i in range(1, N + 1)))
    return u


def periodic_matrix(m, j):
    N = 2 * m + 1
    u = family(m, j)
    rows = [range(1, m + 1), [m + 1], range(m + 2, N + 1)]
    return [[sum(r in {x + (k - 1) // 3 * N for x in u} for r in row)
             for k in (-2, 1, 4)] for row in rows]
