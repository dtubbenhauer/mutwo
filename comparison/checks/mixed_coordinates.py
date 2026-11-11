#!/usr/bin/env python3
"""Exact finite tests of the mixed-coordinate identity; requires compare.py."""
from compare import canonical
import argparse


def endpoint(m, j):
    d = m - j
    return (1,) * (j - 1) + (0,) * d + (-1, 0, 1) + (0,) * d + (-1,) * (j - 1)


def spherical(m, k):
    return (1,) * k + (0,) * (2 * (m - k) + 1) + (-1,) * k


def verify(m):
    print(f'm={m}.  Rows indexed by full-spherical k, columns by upper j=1,...,m.')
    for k in range(m):
        row = []
        for j in range(1, m + 1):
            lhs = canonical(endpoint(m, j)).get(spherical(m, k), {})
            if k < j:
                rhs = canonical(endpoint(m-k, j-k))[spherical(m-k, 0)]
            else:
                rhs = {}
            assert lhs == rhs
            row.append(lhs.get(1, 0))
        print('k=', k, ':', *row)
    polynomial = canonical(endpoint(m, 1))[spherical(m,0)]
    assert polynomial == {d: 1 for d in range(1, 2*m, 2)}
    print('first entry, all powers (degree: coefficient):', dict(sorted(polynomial.items())))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('m', nargs='*', type=int, default=[2,3,4])
    for m in parser.parse_args().m:
        verify(m)
        canonical.cache_clear()
