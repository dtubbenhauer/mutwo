#!/usr/bin/env python3
"""Additional direct affine spherical KL coefficients beyond A's displayed rows."""
import sys
from compare import canonical, length

def check(m, j):
    levels=(1,)*(j-1)+(0,)*(m-j)+(-1,0,1)+(0,)*(m-j)+(-1,)*(j-1)
    expansion=canonical(levels)
    poly=expansion[(0,)*len(levels)]
    print(f'm={m} j={j} length={length(levels)} support={len(expansion)} mu={poly.get(1,0)}',flush=True)

if __name__=='__main__':
    for pair in sys.argv[1:] or ['6,2','7,2','8,2']:
        check(*(int(i) for i in pair.split(',')))
        canonical.cache_clear()
        length.cache_clear()
