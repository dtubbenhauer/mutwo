#!/usr/bin/env python3
"""Independent finite stress tests of generic web interfaces.

These tests do NOT prove the Lean hypotheses or the counterexample.
They enumerate concrete objects without importing the research KL engine.
Run without -O; assertions are the tests.
"""
from pathlib import Path
from itertools import product
from fractions import Fraction
from functools import lru_cache
import json

ROOT = Path(__file__).resolve().parents[1]

@lru_cache(None)
def gauss(n, k, q=2):
    if k < 0 or k > n:
        return 0
    if n == 0:
        return int(k == 0)
    return gauss(n-1,k,q) + q**(n-k)*gauss(n-1,k-1,q)

def qint(n,q=2):
    return sum(q**i for i in range(max(0,n)))

def compositions(n):
    for bits in product((False,True),repeat=n-1):
        cuts=[0]+[i+1 for i,b in enumerate(bits) if b]+[n]
        yield tuple(zip(cuts,cuts[1:]))

def periodic_dimension(A):
    return sum(A[i][c]*A[k][h]*(int(c+1<h)+int(k<=i and c<h))
        for i in range(len(A)) for k in range(len(A))
        for c in range(3) for h in range(3))

def window_audit():
    records=[]
    for n in range(3,8):
        windows=[]
        for shifts in product((-1,0,1),repeat=n):
            if sum(shifts):continue
            w=tuple(sorted((i+1+n*shifts[i] for i in range(n)),reverse=True))
            inv=[None]*n
            for pos,x in enumerate(w,1):
                residue=(x-1)%n
                winding=(x-1)//n
                inv[residue]=pos-n*winding
            inverse_wind=tuple((x-1)//n for x in inv)
            assert set(inverse_wind)<=set((-1,0,1))
            assert all(w[i]>w[i+1] for i in range(n-1))
            length=sum(abs((w[j]-w[i])//n) for i in range(n) for j in range(i+1,n))
            windows.append((w,inv,inverse_wind,length))
        checks=maximal=0
        for blocks in compositions(n):
            labels={}
            for w,inv,wind,length in windows:
                A=tuple(tuple(sum(wind[i]==c-1 for i in range(lo,hi)) for c in range(3))
                    for lo,hi in blocks)
                ismax=all(inv[i]>inv[i+1] for lo,hi in blocks for i in range(lo,hi-1))
                gap=length-n*(n-1)//2
                dim=periodic_dimension(A)
                assert (dim==gap)==ismax,(n,blocks,w,A,dim,gap,ismax)
                assert gap<=dim
                if ismax:
                    assert A not in labels,(n,blocks,A,labels.get(A),w)
                    labels[A]=w
                    maximal+=1
                checks+=1
        records.append(dict(N=n,windows=len(windows),compositions=2**(n-1),
            length_and_converse_checks=checks,maximal_labels=maximal))
    return records

def subspaces(d):
    found={frozenset((0,))}; todo=list(found)
    while todo:
        S=todo.pop()
        for v in range(1<<d):
            if v not in S:
                U=S|frozenset(x^v for x in S)
                if U not in found:
                    found.add(U);todo.append(U)
    return list(found)

def flag_audit():
    records=[]
    for d in range(5):
        allS=subspaces(d)
        dim=lambda S:len(S).bit_length()-1
        checks=0
        for lo in allS:
            if d>0:
                count=sum(dim(H)==d-1 and lo<=H for H in allS)
                assert count==qint(d-dim(lo));checks+=1
            for up in allS:
                if not lo<=up:continue
                interval=[S for S in allS if lo<=S<=up]
                for m in range(d+3):
                    count=sum(dim(S)==m for S in interval)
                    expected=gauss(dim(up)-dim(lo),m-dim(lo))
                    assert count==expected,(d,'subspaces',lo,up,m,count,expected)
                    count=sum(dim(I)==m and dim(K)==m+1 and I<=K
                        for I in interval for K in interval)
                    expected=gauss(dim(up)-dim(lo),m-dim(lo))*qint(dim(up)-m)
                    assert count==expected,(d,'adjacent',lo,up,m,count,expected)
                    checks+=2
        records.append(dict(dimension=d,subspaces=len(allS),formula_checks=checks))
    return records

def rank_one_normalization():
    out=[]
    for p in (2,3,5,7):
        v=Fraction(1,p);q=p*p
        # nil {s}: C_s = H_s+v, gallery singleton for both finite indices.
        assert v**(1-0)==v and v**(1-1)==1
        # {s} -> empty -> {s}: C_s^2 = (v+v^-1) C_s.
        assert v**(2-0)*(q+1)==v*v+1
        assert v**(2-1)*(q+1)==v+1/v
        out.append(dict(p=p,q=q,gallery_card=q+1))
    return out

if __name__=='__main__':
    report=dict(status='experimental independent finite tests; not a Lean proof',
        periodic_matrix=window_audit(),finite_flag_formulas=flag_audit(),
        rank_one_normalization=rank_one_normalization())
    path=ROOT/'reports/fidelity-web-computations.json'
    path.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
