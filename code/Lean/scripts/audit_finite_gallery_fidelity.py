#!/usr/bin/env python3
"""Independent semantic spot-check, NOT a Lean-verified certificate.

Enumerate actual subspaces of F_2^5 and every admissible 3x3 orbit matrix
with margins (2,1,2). Count the manuscript's finite galleries directly as
sets L <= I <= K <= H, then compare both the manuscript's four-case formula
and the polynomial encoded by CanonicalGallery.count. No KL computation
or imported Hecke/flag dictionary is being checked here.
"""
from pathlib import Path
from itertools import product
import json

ROOT=Path(__file__).resolve().parents[1]

def span(basis):
    s=frozenset({0})
    for v in basis:
        s=s|frozenset(x^v for x in s)
    return s

def subspaces(n):
    layers=[{frozenset({0})}]
    for _ in range(n):
        nxt=set()
        for s in layers[-1]:
            for v in range(1<<n):
                if v not in s:
                    nxt.add(s|frozenset(x^v for x in s))
        layers.append(nxt)
    return layers

def qint(n,q=2):
    return sum(q**i for i in range(max(0,n)))

def gauss(n,k,q=2):
    if k<0 or k>n:return 0
    result=1
    numerator=1;denominator=1
    for i in range(k):
        numerator*=q**(n-i)-1
        denominator*=q**(k-i)-1
    assert numerator%denominator==0
    return numerator//denominator

def parts3(n):
    return [(a,b,n-a-b) for a in range(n+1) for b in range(n-a+1)]

def check():
    m=2;n=5;spaces=subspaces(n)
    assert [len(s) for s in spaces]==[1,31,155,155,31,1]
    F=span([1,2]);Fp=span([1,2,4])
    lines=[s for s in spaces[1] if s<=F]
    hypers=[s for s in spaces[4] if Fp<=s]
    flags=[(I,K) for I in spaces[m] for K in spaces[m+1] if I<=K]
    rows=[]
    for A in product(parts3(m),parts3(1),parts3(m)):
        r=sum(row[0] for row in A)
        if r!=sum(row[2] for row in A):continue
        indices=[[],[],[]];i=0
        for row in A:
            for col,size in enumerate(row):
                indices[col]+=list(range(i,i+size));i+=size
        I0=span([1<<i for i in indices[0]])
        K0=span([1<<i for i in indices[0]+indices[1]])
        actual=[[0,0],[0,0]]
        for I,K in flags:
            if not I0<=I or not K<=K0:continue
            for L in lines:
                if not L<=I:continue
                for H in hypers:
                    if K<=H:actual[int(not L<=I0)][int(not K0<=H)]+=1
        l=m-r;a=A[0][0];b=a+A[1][0]
        c=m-A[0][2];d=m+1-A[0][2]-A[1][2]
        L=[qint(a),qint(c)-qint(a)]
        H=[qint(d-l-1),qint(l+b)-qint(d-l-1)]
        paper=[[L[e]*H[t]*gauss(n-2*r-e-t,m-r-e)*qint(m+1-r-t)
                for t in (0,1)] for e in (0,1)]
        assert actual==paper,(A,actual,paper)
        s=A[1][2]+A[2][2];beta=A[1][0];delta=A[1][0]+A[1][1]
        encoded=(qint(l)*(qint(l+a+beta)-qint(s+delta-1))*qint(a)*gauss(2*l,l)
          +qint(l)*(qint(l+a+beta)-qint(s+delta-1))*(qint(l+s)-qint(a))*gauss(2*l-1,l-1)
          +qint(l+1)*qint(s+delta-1)*qint(a)*gauss(2*l+1,l)
          +qint(l+1)*qint(s+delta-1)*(qint(l+s)-qint(a))*gauss(2*l,l-1))
        total=sum(map(sum,actual))
        assert encoded==total,(A,encoded,total)
        rows.append(dict(matrix=A,rank=r,corank=l,four_case_counts=actual,count=total))
    output=dict(status='experimental direct finite-set enumeration; not a Lean certificate',
      field_cardinality=2,ambient_dimension=5,subspace_counts=[len(s) for s in spaces],
      tested_matrices=len(rows),all_four_case_counts_match=True,
      all_lean_polynomial_encodings_match=True,cases=rows)
    (ROOT/'reports/fidelity-finite-gallery.json').write_text(json.dumps(output,indent=2)+'\n')
    print({k:v for k,v in output.items() if k!='cases'})

if __name__=='__main__':check()
