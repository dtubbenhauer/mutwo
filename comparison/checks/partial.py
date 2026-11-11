#!/usr/bin/env python3
"""Independent checks of the partial-row proof. Run with python3 partial.py 2 3 4 5."""
import argparse
import compare as c

def verify(m):
    n=2*m+1
    S=frozenset(range(n))
    I=S-{0}
    E=I-{1,2}
    Q1=frozenset(range(2,m+1))
    Q2=frozenset(range(1,m))
    e=(0,)*n
    def post(F):
        return c.average(c.average(F,Q1,Q1&E),Q2,Q1&Q2)
    def J(j):
        return S-{j,j+1}
    def K(j):
        return I-{1,j+1}
    def row(i):
        return (1,)*(i-1)+(0,)*(m-i)+(-1,0,1)+(0,)*(m-i)+(-1,)*(i-1)
    def sphere(i):
        return (1,)*i+(0,)*(n-2*i)+(-1,)*i
    def gs(k):
        from math import comb
        return {sign*(2*k-3-2*t):comb(t+3,3) for t in range(k-1) for sign in (-1,1)}
    prefix={}
    values=[]
    for j in range(1,m+1):
        z=(-1,0)+(1,)*j+(0,)*(n-2*j-1)+(-1,)*(j-1)
        c.accumulate(prefix,c.canonical(z))
        T=post(c.gallery(n,[J(j),K(j),E]))
        U=post(prefix)
        if j==m:
            assert U==T
        if m<=4:
            expanded=c.canonical_coefficients(U)
            for r in range(m+1):
                assert expanded.get(sphere(r),{})==gs(j-r)
                if r:
                    assert expanded.get(row(r),{})==({0:1} if r<=j else {})

        for r in range(j+1):
            a=m-r; k=j-r
            if k==0:
                assert sphere(r) not in T
                continue
            nn=2*a+1
            ss=frozenset(range(nn)); ii=ss-{0}
            # Scalar at mixed gallery's origin, from its actual normalized
            # product. The BC/Psi ratio follows from averaging at the origin.
            reduced=c.gallery(nn,[ss-{k,k+1}, ii-{1,k+1}, ii-{1,2}])
            quantum_a={t:1 for t in range(1-a,a,2)}
            origin=c.times(c.times(reduced[(0,)*nn],quantum_a),quantum_a)
            assert T[sphere(r)]==origin
            diff=origin.copy(); c.plus(diff,U.get(sphere(r),{}),scale=-1)
            assert not diff or min(diff)>=5
        # Evaluate U's rank-wise spherical residual directly. Each term
        # below is a separately computed canonical transition polynomial.
        rem=U[e].copy()
        for r in range(j-1):
            c.plus(rem,c.times(gs(j-r),c.canonical(sphere(r))[e]),scale=-1)
        value=c.canonical(row(j))[e].get(1,0)
        values.append(value)
        print(f'm={m} j={j} raw spherical restrictions and correction-depth checks pass; '
              f'residual [v]={rem.get(1,0)}, KL row entry={value}',flush=True)
        assert min(rem)==1 and rem[1]==j*(j+1)//2 and value==j
    for f in [c.canonical,c.length,c.rearrangements]:
        f.cache_clear()
    print('row',m,values,flush=True)

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('ranks',nargs='*',type=int,default=[2,3,4])
    for m in parser.parse_args().ranks:
        verify(m)
