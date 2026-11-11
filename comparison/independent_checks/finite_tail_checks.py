#!/usr/bin/env python3
"""Compare the two finite tails BEFORE applying the common affine prefix.

The engine's minimal-coset test is explicitly set to the left parabolic V
for each independent calculation. It is reset between ranks; no formulas
for canonical expansions are supplied to the recursive KL algorithm.
"""
import affine_hecke as h
from pathlib import Path
OUTPUT = Path(__file__).resolve().parent / 'output'
OUTPUT.mkdir(parents=True, exist_ok=True)

for r in (2,3,4,5):
    n=2*r+1; e=tuple(range(1,n+1)); I=set(range(1,n))
    V=I-{r,r+1}; KA=set(range(2,n-1)); KB=I-{1,r+1}; E=set(range(3,n))
    def minimal_V(w):
        z=h.inv(w)
        return all(z[t-1]<z[t] for t in V)
    h.minimal=minimal_V
    h.action.cache_clear()
    def sequence(Qs):
        F={e:{0:1}}; P=V
        for Q in Qs: F=h.step(F,P,Q); P=Q
        return F
    a=sequence([KA,V]); b=sequence([KB,E]); kl=h.KL(n)
    ca=kl.decompose(a); cb=kl.decompose(b)
    wV=list(range(1,n+1)); wV[:r]=reversed(wV[:r]);wV[r+1:]=reversed(wV[r+1:]);wV=tuple(wV)
    expected_a=list(range(n,0,-1));expected_a[r-1:r+2]=sorted(expected_a[r-1:r+2]);expected_a=tuple(expected_a)
    expected_b=(r,r+1,*range(n,r+1,-1),*range(r-1,0,-1))
    a_rep=h.mul(wV,expected_a); b_rep=h.mul(wV,expected_b)
    assert ca=={a_rep:{0:1}} and cb=={b_rep:{0:1}}
    print('rank',r,'a support',len(a),'b support',len(b),'a canonical',ca=={a_rep:{0:1}},'b canonical',cb=={b_rep:{0:1}},flush=True)
    print('ordinary a upper',expected_a,'ordinary b upper',expected_b,flush=True)
    F=b
    for s in tuple(range(2,r+1))+tuple(range(1,r)): F=h.C(F,s)
    diff=kl.decompose(h.v_add(F,a,{0:-1}))
    assert all(c>=0 for p in diff.values() for c in p.values())
    print('b*chain-a canonical terms',len(diff),'positive',all(c>=0 for p in diff.values() for c in p.values()),flush=True)
    for w,p in sorted(diff.items(),key=lambda kv:(h.length(kv[0]),kv[0]),reverse=True):
        print('minimal V window',w,'ordinary upper',h.mul(wV,w),'coefficient',h.p_str(p),flush=True)
    h.savevec(diff,OUTPUT / f'r{r}_finite_tail_difference.json')
