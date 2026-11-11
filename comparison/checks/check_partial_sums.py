#!/usr/bin/env python3
"""Check the low-degree full-spherical triangular system, not a KL recursion.
Standalone standard library. Ranges 1<=j<=m<=20. The monomials are v-powers.
"""
from functools import cache
from math import comb
from itertools import product

def add(a,b,c=1):
    out=a.copy()
    for i,x in b.items():
        out[i]=out.get(i,0)+c*x
        if not out[i]: del out[i]
    return out

@cache
def gauss(n,k):
    if k<0 or k>n:return {}
    if k==0:return {0:1}
    return add(gauss(n-1,k-1),{i+2*k:x for i,x in gauss(n-1,k).items()})

def mul(a,b,ceiling):
    out={}
    for (u,x),(v,y) in product(a.items(),b.items()):
        if u+v<=ceiling:out[u+v]=out.get(u+v,0)+x*y
    return {i:x for i,x in out.items() if x}

def ambient_coordinate(n,k):
    """Raw BS_j T coefficient at Theta_r in positive Gaussian parameter."""
    if not k:return {}
    a={3-2*k:1}
    for f in [gauss(n,1),gauss(n,1),gauss(k,1),gauss(2*n-1,k-1)]:
        a=mul(a,f,1)
    return a

def g(k):
    return {d*e:comb(h+3,3) for h in range(k-1)
            for e in [2*k-3-2*h] for d in [-1,1]}

def test(m,j):
    seen=[]
    for r in reversed(range(j+1)):
        n,k=m-r,j-r
        coefficient=ambient_coordinate(n,k)
        for s,weight in seen:
            h=s-r
            kernel=add(gauss(2*n+1,h),gauss(2*n+1,h-1),-1)
            coefficient=add(coefficient,mul(weight,kernel,1),-1)
        weight={d:x for d,x in coefficient.items() if d<=0}
        weight.update({-d:x for d,x in weight.items() if d<0})
        assert weight==g(k),(m,j,r,'spherical correction')
        seen.append((r,weight))
        assert coefficient.get(1,0)-weight.get(1,0)==k*(k+1)//2, (m,j,r)
    return len(seen)

if __name__=='__main__':
    count=0
    for m in range(1,21):
        for j in range(1,m+1):count+=test(m,j)
    print('All',count,'(m,j,r) triangular tests passed, 1 <= j <= m <= 20.')
    print('These test standard-coordinate arithmetic, independently of canonical-basis enumeration.')
