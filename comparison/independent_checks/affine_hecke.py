#!/usr/bin/env python3
"""Exact affine A spherical Hecke calculations, using integer Laurent polynomials.

The routines compute KL polynomials and product expansions from the Hecke relations.
Windows act as functions; H_s^2=1+(v^-1-v)H_s, C_s=H_s+v.
Spherical standards are M_x=C_I H_x for minimal left I-coset x.
"""
from collections import deque
from functools import lru_cache
import json

def p_add(a,b):
    c=a.copy()
    for k,v in b.items():
        c[k]=c.get(k,0)+v
        if not c[k]: del c[k]
    return c
def p_mul(a,b):
    c={}
    for i,x in a.items():
        for j,y in b.items(): c[i+j]=c.get(i+j,0)+x*y
    return {k:v for k,v in c.items() if v}
def shift(a,d,c=1): return {k+d:v*c for k,v in a.items() if v*c}
def p_str(p):
    if not p: return '0'
    return ' + '.join(str(c) if d==0 else (('' if c==1 else str(c)+'*')+'v^'+str(d)) for d,c in sorted(p.items()))
def v_add(a,b,scalar={0:1}):
    c={w:p.copy() for w,p in a.items()}
    for w,p in b.items():
        c[w]=p_add(c.get(w,{}),p_mul(scalar,p))
        if not c[w]: del c[w]
    return c
def at(w,i):
    q,r=divmod(i-1,len(w)); return w[r]+q*len(w)
def mul(x,y): return tuple(at(x,i) for i in y)
def inv(w):
    z=[0]*len(w)
    for i,v in enumerate(w,1):
        q,r=divmod(v-1,len(w)); z[r]=i-q*len(w)
    return tuple(z)
@lru_cache(None)
def length(w):
    n=len(w)
    return sum(abs((w[j]-w[i])//n) for i in range(n) for j in range(i+1,n))
def rs(w,s):
    z=list(w)
    if s==0: z[0],z[-1]=z[-1]-len(w),z[0]+len(w)
    else: z[s-1],z[s]=z[s],z[s-1]
    return tuple(z)
@lru_cache(None)
def minimal(w):
    z=inv(w); return all(a<b for a,b in zip(z,z[1:]))
@lru_cache(None)
def action(w,s):
    x=rs(w,s)
    if not minimal(x): return ((w,{-1:1}),)
    if length(x)>length(w): return ((x,{0:1}),)
    return ((x,{0:1}),(w,{-1:1,1:-1}))
def H(F,s):
    G={}
    for w,p in F.items():
        for x,q in action(w,s):
            G[x]=p_add(G.get(x,{}),p_mul(p,q))
            if not G[x]: del G[x]
    return G
def C(F,s): return v_add(H(F,s),F,{1:1})
def wordH(F,word):
    for s in word: F=H(F,s)
    return F
@lru_cache(None)
def group(n,P):
    e=tuple(range(1,n+1)); seen={e:()}; q=deque([e])
    while q:
        w=q.popleft()
        for s in P:
            x=rs(w,s)
            if x not in seen: seen[x]=seen[w]+(s,); q.append(x)
    return seen
@lru_cache(None)
def quotient(n,P,T):
    # Enumerate the quotient directly: every reduced prefix of a minimal
    # left-coset representative is again minimal. No factorial-size group
    # enumeration is needed. Components of P are finite A paths.
    def longest(P):
        todo=set(P); result=0
        while todo:
            stack=[todo.pop()]; count=0
            while stack:
                s=stack.pop(); count+=1
                for t in ((s-1)%n,(s+1)%n):
                    if t in todo: todo.remove(t); stack.append(t)
            result+=count*(count+1)//2
        return result
    L=longest(P); LT=longest(T)
    e=tuple(range(1,n+1)); seen={e:()}; q=deque([e])
    while q:
        w=q.popleft()
        for s in P:
            x=rs(w,s)
            if x in seen: continue
            lx=length(x)
            if all(length(rs(inv(x),t))>lx for t in T):
                seen[x]=seen[w]+(s,); q.append(x)
    return tuple((word,L-LT-len(word)) for word in seen.values())
def step(F,P,Q):
    n=len(next(iter(F))); T=tuple(sorted(set(P)&set(Q)))
    G={}
    for word,d in quotient(n,tuple(sorted(Q)),T):
        G=v_add(G,wordH(F,word),{d:1})
    return G
def D(n,chain):
    P=tuple(range(1,n)); F={tuple(range(1,n+1)):{0:1}}
    for Q in chain:
        F=step(F,P,Q); P=Q
    return F

class KL:
    """Canonical triangular elimination in the spherical standard basis."""
    def __init__(self,n):
        self.n=n; self.e=tuple(range(1,n+1)); self.cache={self.e:{self.e:{0:1}}}
    def get(self,w):
        if w in self.cache: return self.cache[w]
        assert minimal(w)
        s=next(s for s in range(self.n) if length(rs(w,s))<length(w))
        z=rs(w,s); F=C(self.get(z),s)
        # A bar-invariant scalar is determined by its powers <=0.
        for x in sorted(F,key=lambda x:(length(x),x),reverse=True):
            if x==w: continue
            p=F.get(x,{})
            correction={}
            for d,c in p.items():
                if d<=0:
                    correction[d]=c
                    if d<0: correction[-d]=c
            if correction: F=v_add(F,self.get(x),shift(correction,0,-1))
        assert F[w]=={0:1}
        assert all(min(p)>0 for x,p in F.items() if x!=w)
        self.cache[w]=F
        return F
    def decompose(self,F):
        G={w:p.copy() for w,p in F.items()}; coeff={}
        for w in sorted(G,key=lambda w:(length(w),w),reverse=True):
            if w not in G: continue
            p=G[w]; coeff[w]=p
            G=v_add(G,self.get(w),shift(p,0,-1))
        assert not G
        return coeff

def endpoints(m,j=None):
    n=2*m+1; j=m if j is None else j
    lo=set(range(1,j))|{m+2}; hi={m}|set(range(n-j+2,n+1))
    u=tuple(sorted(i+n*((i in hi)-(i in lo)) for i in range(1,n+1)))
    return inv(u)
def constructions(r):
    n=2*r+1; S=set(range(n)); I=S-{0}
    J=lambda j:S-{j,j+1}
    E=set(range(3,n)); V=I&J(r); KA=set(range(2,n-1))
    KB=lambda j:I-{1,j+1}
    A=D(n,[J(r),KA,V])
    B=D(n,[J(r),KB(r),E])
    Bprev=D(n,[J(r-1),KB(r-1),E])
    corrected=v_add(B,Bprev,{0:-1})
    extras=[]
    for s in range(2,r):
        X=D(n,[S-{s},E]); extras.append(X)
        corrected=v_add(corrected,X,{-1:1,1:1})
    return A,B,Bprev,extras,corrected

def savevec(F,path):
    with open(path,'w') as f: json.dump({','.join(map(str,w)):{str(k):v for k,v in sorted(p.items())} for w,p in sorted(F.items())},f,indent=2)
