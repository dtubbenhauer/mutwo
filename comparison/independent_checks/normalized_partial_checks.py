#!/usr/bin/env python3
"""Phase-II audit of the linked comparison note's normalized-tail/partial sums.

Only the parabolic subsets are taken as input; the normalization is implemented
by actual minimal-coset sums. Canonical vectors use our independent KL recursion.
"""
from affine_hecke import *
from math import comb
import sys,time
from pathlib import Path
OUTPUT = Path(__file__).resolve().parent / 'output'
OUTPUT.mkdir(parents=True, exist_ok=True)

def word_window(n,word):
    t=word.count('A'); counts={'A':0,'B':0,'C':0}; result=[]
    for a in word:
        counts[a]+=1
        result.append(counts[a]+{'A':-t,'B':t,'C':n}[a])
    return tuple(result)

def g(k):
    if k<=1:return {}
    result={}
    for a in range(k-1):
        d=2*k-3-2*a;c=comb(a+3,3)
        result[d]=c;result[-d]=c
    return result

for m in map(int,sys.argv[1:] or [2,3,4]):
    start=time.time();n=2*m+1;S=set(range(n));I=S-{0};E=set(range(3,n));V=I-{m,m+1}
    e=tuple(range(1,n+1));Q1=set(range(2,m+1));Q2=set(range(1,m));KB=I-{1,m+1}
    def T(F):return step(step(F,E,Q1),Q1,Q2) if F else {}
    A,B,_,_,_=constructions(m)
    completed=T(B)
    assert completed==A
    complete_gallery=step(step(B,E,KB),KB,V)
    assert complete_gallery==A
    print('m',m,'full normalized identity A=B*T: True; five-target gallery equality: True; standard support',len(A),flush=True)
    if m==3:
        Z=v_add(C(C(B,2),3),B,{0:-1})
        assert v_add(C(C(Z,1),2),Z,{0:-1})==A
        print(' m3 relative-word identity A=B(C2C3-1)(C1C2-1): True',flush=True)
    kl=KL(n);Phi={};Ys=[]
    for j in range(1,m+1):
        X=word_window(n,'AB'+'C'*j+'B'*(n-2*j-1)+'A'*(j-1))
        Phi=v_add(Phi,kl.get(X));Y=T(Phi);Ys.append(Y)
        Cdec=kl.decompose(Y)
        Fmult=[Cdec.get(endpoints(m,i),{}) for i in range(1,m+1)]
        expectedF=[{0:1} if i<=j else {} for i in range(1,m+1)]
        assert Fmult==expectedF
        spherical={}
        for r in range(m+1):
            Z=word_window(n,'C'*r+'B'*(n-2*r)+'A'*r)
            got=Cdec.get(Z,{})
            assert got==g(j-r),(m,j,r,got,g(j-r))
            if got:spherical=v_add(spherical,kl.get(Z),got)
        residual=v_add(Y,spherical,{0:-1})
        mu_sum=residual.get(e,{}).get(1,0)
        assert mu_sum==comb(j+1,2)
        other=residual
        for i in range(1,j+1):other=v_add(other,kl.get(endpoints(m,i)),{0:-1})
        origin_other=other.get(e,{})
        assert not origin_other or min(origin_other)>=3
        BSj=D(n,[S-{j,j+1},I-{1,j+1},E])
        decompBS=kl.decompose(BSj)
        phi_rest=v_add(BSj,Phi,{0:-1});restC=kl.decompose(phi_rest)
        allowedD={word_window(n,'AA'+'C'*s+'B'*(n-2*s)+'A'*(s-2)):s for s in range(2,min(j,m-1)+1)}
        assert all(w in allowedD for w in restC)
        assert all(min(p)>=2-n+2*j for p in restC.values())
        diff=T(phi_rest)
        # At spherical standards, discarded seed terms start in degree >=5.
        discarded_vals=[]
        for r in range(j):
            Z=word_window(n,'C'*r+'B'*(n-2*r)+'A'*r)
            p=diff.get(Z,{})
            discarded_vals.append(min(p) if p else None)
            assert not p or min(p)>=5
        print(' j',j,'canonical terms',len(Cdec),'F multiplicities',[p.get(0,0) for p in Fmult],
              'spherical multiplicities g_(j-r): True; residual [v]',mu_sum,
              'other origin valuation',min(origin_other) if origin_other else None,
              'discarded spherical valuations',discarded_vals,flush=True)
        print('  Y_j[e]=',p_str(Y.get(e,{})),flush=True)
        print('  residual[e]=',p_str(residual.get(e,{})),flush=True)
        savevec(Cdec,OUTPUT / f'phase2_m{m}_Y{j}_canonical.json')
        savevec(decompBS,OUTPUT / f'phase2_m{m}_BS{j}_canonical.json')
    assert Ys[-1]==A
    print('elapsed',round(time.time()-start,3),flush=True)
