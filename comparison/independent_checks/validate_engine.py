#!/usr/bin/env python3
"""Basic engine tests independent of the identities asserted in A and B."""
from affine_hecke import *

for n in (5,7):
    e=tuple(range(1,n+1)); sample={e}
    for depth in range(5):
        sample |= {rs(w,s) for w in tuple(sample) for s in range(n) if minimal(rs(w,s))}
    for w in sample:
        assert mul(w,inv(w))==e and mul(inv(w),w)==e
        F={w:{0:1}}
        for s in range(n):
            assert H(H(F,s),s)==v_add(F,H(F,s),{-1:1,1:-1})
            for t in range(n):
                if s==t: continue
                if (s-t)%n in (1,n-1):
                    assert H(H(H(F,s),t),s)==H(H(H(F,t),s),t)
                else: assert H(H(F,s),t)==H(H(F,t),s)
    # Compare optimized quotient enumeration to exhaustive finite groups.
    for P,T in [((0,1,2),(1,2)),((0,1,3),(1,3)),((1,2,3),(1,3))]:
        allw=group(n,P); allt=group(n,T)
        L=max(map(len,allw.values())); LT=max(map(len,allt.values()))
        expected={w:L-LT-len(word) for w,word in allw.items() if all(length(rs(inv(w),t))>len(word) for t in T)}
        actual={}
        for word,d in quotient(n,P,T):
            w=e
            for s in word: w=rs(w,s)
            actual[w]=d
        assert actual==expected
    print('N',n,': inverse, Hecke quadratic, braid and commuting relations on',len(sample),'spherical standards; exhaustive quotient cross-checks passed')
