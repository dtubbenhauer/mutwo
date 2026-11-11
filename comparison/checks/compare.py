#!/usr/bin/env python3
"""Exact spherical affine type A calculation. Python 3.10+, standard library."""
from collections import Counter, defaultdict
from functools import cache
from itertools import product
import argparse

# Sparse Laurent polynomials over the integers, keyed by exponent.
ONE = {0: 1}
ETA = {-1: 1, 1: 1}

def plus(p, q, scale=1, shift=0):
    """In-place p += scale * v^shift * q. Keep no zero coefficients."""
    for degree, coeff in q.items():
        key = degree + shift
        p[key] = p.get(key, 0) + scale * coeff
        if not p[key]:
            del p[key]

def times(p, q):
    result = {}
    for degree, coeff in p.items():
        plus(result, q, coeff, degree)
    return result

def quotient(p, q):
    """Exact division by a Laurent polynomial with unit top coefficient."""
    if not p or q == ONE:
        return p
    result = {}
    rem = p.copy()
    hi = max(q)
    lo = min(p) - min(q)
    while rem and max(rem) - hi >= lo:
        d = max(rem) - hi
        assert q[hi] == 1
        c = rem[d + hi]
        result[d] = c
        plus(rem, q, -c, d)
    assert not rem, ('nonexact division', p, q)
    return result

def accumulate(F, G, scale=1, shift=0):
    for x, p in G.items():
        dest = F.setdefault(x, {})
        plus(dest, p, scale, shift)
        if not dest:
            del F[x]
    return F

def product_by_scalar(F, p):
    return {x: times(c, p) for x, c in F.items()}

def show(p):
    """Output Laurent polynomial as a degree:coefficient dictionary."""
    return dict(sorted(p.items()))

@cache
def blocks(n, P):
    """Positions (0-based); cut immediately after an omitted reflection.
    Second component is the +N period shift of the unwrapped position."""
    cut = next(k for k in range(n) if k not in P)
    groups = []
    block = []
    for pos in range(cut, cut+n):
        block.append((pos % n, pos // n))
        if (pos+1) % n not in P:
            groups.append(tuple(block))
            block = []
    assert not block
    return tuple(groups)

@cache
def factorial(k):
    if k < 2:
        return ONE
    return times(factorial(k-1), {d: 1 for d in range(1-k, k, 2)})

def factorial_product(sizes):
    p = ONE
    for k in sizes:
        p = times(p, factorial(k))
    return p

def poincare(n, P):
    return factorial_product(len(b) for b in blocks(n, P))

def inversions(a):
    return sum(x > y for i, x in enumerate(a) for y in a[i+1:])

@cache
def rearrangements(values):
    if not values:
        return (((), 0),)
    result = []
    for first in sorted(set(values)):
        i = values.index(first)
        for tail, inv in rearrangements(values[:i] + values[i+1:]):
            result.append(((first,) + tail, inv+i))
    return tuple(result)

def average(F, P, overlap=frozenset()):
    """F * C_P / pi_overlap, with an exact division for each coefficient."""
    n = len(next(iter(F)))
    bs = blocks(n, frozenset(P))
    denom = poincare(n, frozenset(overlap))
    orbits = defaultdict(dict)
    for x, p in F.items():
        local = tuple(tuple(x[i] + turn for i, turn in b) for b in bs)
        key = tuple(tuple(sorted(u)) for u in local)
        plus(orbits[key], p, shift=-sum(map(inversions, local)))
    out = {}
    for key, p in orbits.items():
        stabilizer = factorial_product(c for u in key for c in Counter(u).values())
        base = quotient(times(p, stabilizer), denom)
        if not base:
            continue
        top = sum(sum(a != b for i,a in enumerate(u) for b in u[i+1:]) for u in key)
        for choice in product(*(rearrangements(u) for u in key)):
            x = [0]*n
            d = 0
            for b, (u, inv) in zip(bs, choice):
                for (i, turn), val in zip(b, u):
                    x[i] = val-turn
                d += inv
            out[tuple(x)] = {k + top - d: c for k, c in base.items()}
    return out

def gallery(n, path):
    old = frozenset(range(1,n))
    F = {(0,)*n: ONE}
    for P in path:
        F = average(F, P, old & P)
        old = P
    return F

def right(x,s):
    """Return the minimal representative of W_I x s and comparison sign.
    A level at i is floor((x(i)-1)/N); reconstruction assigns increasing
    residues within levels, beginning with the highest level."""
    n = len(x)
    i,j = (s-1)%n, s%n
    turn = int(s==0)
    a,b = x[i], x[j]+turn
    if a == b:
        return x,0
    y=list(x)
    y[i],y[j] = b,a-turn
    return tuple(y), (1 if a<b else -1)

def mul_simple(F,s):
    """Right multiplication by H_s+v in the spherical standard basis."""
    out = {}
    for x, p in F.items():
        y, sign = right(x,s)
        if sign:
            plus(out.setdefault(y,{}), p)
            plus(out.setdefault(x,{}), p, shift=sign)
        else:
            for d in (-1,1):
                plus(out.setdefault(x,{}), p, shift=d)
    return {x:c for x,c in out.items() if c}

@cache
def length(x):
    for s in range(len(x)):
        y, sign = right(x,s)
        if sign < 0:
            return 1 + length(y)
    assert set(x)=={0}
    return 0

@cache
def canonical(x):
    """Independent spherical KL recursion; only the simple action is used."""
    if not any(x):
        return {x: ONE}
    for s in range(len(x)):
        y, sign = right(x,s)
        if sign<0:
            break
    else:
        raise ValueError(x)
    F = mul_simple(canonical(y),s)
    assert F[x] == ONE
    # In M_y C_s all lower coefficients are polynomials. Removing their
    # constant terms times canonical vectors removes all forbidden degrees.
    corrections = [(z, p[0]) for z,p in F.items() if z!=x and 0 in p]
    for z,k in corrections:
        accumulate(F,canonical(z),scale=-k)
    assert all(all(d>0 and k>0 for d,k in p.items()) for z,p in F.items() if z!=x)
    return F

def canonical_coefficients(F):
    """Triangular elimination. Input monomials may have negative degrees."""
    rem = {x:p.copy() for x,p in F.items()}
    result = {}
    for x in sorted(rem,key=length,reverse=True):
        if x not in rem:
            continue
        p = rem[x].copy()
        result[x] = p
        for d,k in p.items():
            accumulate(rem,canonical(x),scale=-k,shift=d)
    assert not rem
    return result

def word(x):
    return ''.join({1: 'C',0:'B',-1:'A'}[k] for k in x)

def verify(m, full):
    n=2*m+1
    S=frozenset(range(n))
    I=S-{0}
    J=lambda j:S-{j,j+1}
    K=lambda j:I-{1,j+1}
    E=I-{1,2}
    V=I & J(m)
    K_A=I-{1,n-1}
    e=(0,)*n
    row=lambda j: tuple(-1 if i in {m,*range(n-j+2,n+1)} else 1 if i in {*range(1,j),m+2} else 0 for i in range(1,n+1))
    X=(-1,0)+(1,)*m+(-1,)*(m-1)
    beta=row(m)
    A=gallery(n,[J(m),K_A,V])
    B=gallery(n,[J(m),K(m),E])
    prev=gallery(n,[J(m-1),K(m-1),E])
    seed={x:p.copy() for x,p in B.items()}
    accumulate(seed,prev,scale=-1)
    for j in range(2,m):
        tmp=gallery(n,[S-{j},E])
        for d in (-1,1):
            accumulate(seed,tmp,shift=d)
    assert seed == canonical(X)
    raw=B
    running=seed
    endpoint=X
    for s in (*range(2,m+1),*range(1,m)):
        raw=mul_simple(raw,s)
        running=mul_simple(running,s)
        endpoint,sign=right(endpoint,s)
        assert sign==1
    assert endpoint==beta
    Q1=frozenset(range(2,m+1))
    Q2=frozenset(range(1,m))
    def compressed(F):
        return average(average(F,Q1,E & Q1),Q2,Q1 & Q2)
    assert compressed(B)==A
    corrected_compressed=compressed(seed)
    Cbeta=canonical(beta)
    piV=poincare(n,V)
    assert average(Cbeta,V)==product_by_scalar(Cbeta,piV)
    print(f'\nm={m} (letters A,B,C encode levels -1,0,+1).')
    print('Identity coordinates are Laurent dictionaries {degree: coefficient}.')
    print('seed canonical identity check:',seed==canonical(X))
    for nm,F in [('A',A),('B',B),('seed',seed),('rawB_chains',raw),('seed_chains',running),('seed_compressed',corrected_compressed),('Cbeta',Cbeta)]:
        print(nm,'support',len(F),'[M_e]',show(F[e]),'[M_beta]',show(F.get(beta,{})))
    print('row [v] [M_e] C_{u^-1}:',[canonical(row(j))[e].get(1,0) for j in range(1,m+1)])
    for nm,F in [('rawB_chains',raw),('seed_chains',running),('seed_compressed',corrected_compressed),('Cbeta',Cbeta)]:
        PF=average(F,V)
        # Proportionality over Q(v) after the right boundary projectors;
        # test first at e and beta, then throughout vector at every index.
        cross1=times(PF[e],A[beta])
        cross2=times(A[e],PF[beta])
        plus(cross1,cross2,scale=-1)
        same=all(times(PF.get(z,{}),A[beta])==times(A.get(z,{}),PF[beta]) for z in A.keys()|PF.keys())
        print(nm,'equals A?',F==A,'projected proportional to A?',same,'e/beta minor at v=1',sum(cross1.values()))
    if full:
        print('raw compressed chains equal A:', compressed(B)==A)
        print('corrected compressed chains equal Cbeta:', corrected_compressed==Cbeta)
        for nm,F in [('A',A),('rawB_chains',raw),('seed_chains',running),('seed_compressed',corrected_compressed)]:
            coeffs=canonical_coefficients(F)
            print(nm,'canonical summands',len(coeffs),'family-F multiplicities',[(word(row(j)),show(coeffs.get(row(j),{}))) for j in range(1,m+1)])
        for j in range(1,m):
            partial=compressed(gallery(n,[J(j),K(j),E]))
            coeffs=canonical_coefficients(partial)
            print('compressed BS_'+str(j), 'summands',len(coeffs),'family-F',
                  [show(coeffs.get(row(i),{})) for i in range(1,m+1)])
        for j in range(2,m):
            coeffs=canonical_coefficients(compressed(gallery(n,[S-{j},E])))
            print('compressed CBS_'+str(j),'summands',len(coeffs),'family-F',
                  [show(coeffs.get(row(i),{})) for i in range(1,m+1)])
    canonical.cache_clear()
    length.cache_clear()
    rearrangements.cache_clear()

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('ranks',type=int,nargs='*',default=[2,3,4])
    ap.add_argument('--full',action='store_true',help='also decompose three whole products; ranks 2 and 3 are quick')
    args=ap.parse_args()
    for m in args.ranks:
        verify(m,args.full)
