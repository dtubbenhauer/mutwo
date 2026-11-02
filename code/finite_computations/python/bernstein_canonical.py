"""Exact affine canonical vectors directly in the Bernstein polynomial model.

This implementation transports the supplied canonical-product
recursion through an independently implemented Demazure--Lusztig polynomial
action. It avoids triangular inversion of thousands of monomial images.
No value of mu or formula for a canonical polynomial is assumed.

Finite action (q=v) is
 H_i f = v^-1 s_i(f) + (v^-1-v)(f-s_i(f))/(1-X_i/X_(i+1)).
Tau = X_1 H_1 ... H_(N-1), H_0=tau H_(N-1) tau^-1.
The spherical cyclic vector is the constant polynomial 1.
"""
from pathlib import Path
import argparse
from collections import OrderedDict
from functools import lru_cache
import hashlib
import itertools
import json
import pickle
import sys
import time
import tempfile
import zlib

HERE = Path(__file__).resolve().parent
CODE = HERE
DATA = HERE.parent / 'data'
DATA.mkdir(exist_ok=True)
sys.path.insert(0, str(CODE))
from guralnick_candidate_kl import PackedKL
from spherical_web import family, plus, add_vector, json_poly


class PolynomialCanonical:
    def __init__(self, m, max_j=None, cache_mib=256):
        self.m=m
        self.N=2*m+1
        j=m if max_j is None else max_j
        self.D=2*j*(self.N-j)-2*(m-j)-3
        self.kl=PackedKL(self.N-1,self.D,cache_mib=cache_mib)
        self.zero=(0,)*self.N
        self.cache=OrderedDict([(self.kl.e,{self.zero:{0:1}})])
        self.cache_limit=cache_mib*1024**2
        self.cache_bytes=256
        self.cache_sizes={self.kl.e:256}
        self._temporary_cache=tempfile.TemporaryDirectory(prefix=f'affine-web-m{m}-')
        self.disk=Path(self._temporary_cache.name)
        self.files={}
        self.computed=0
        self.last=time.monotonic()
        self.start=self.last

    @staticmethod
    def add_term(out, delta, p, scalar=1, shift=0):
        target=out.setdefault(delta,{})
        plus(target,p,scale=scalar,shift=shift)
        if not target:del out[delta]

    def finite_h(self, vector, i, inverse=False):
        out={}
        for delta,p in vector.items():
            a,b=delta[i-1],delta[i]
            swapped=list(delta);swapped[i-1],swapped[i]=b,a
            self.add_term(out,tuple(swapped),p,shift=-1)
            if a>b:
                for k in range(a-b):
                    term=list(delta);term[i-1],term[i]=a-1-k,b+1+k
                    self.add_term(out,tuple(term),p,shift=1)
                    self.add_term(out,tuple(term),p,scalar=-1,shift=-1)
            elif a<b:
                for k in range(b-a):
                    term=list(delta);term[i-1],term[i]=b-1-k,a+1+k
                    self.add_term(out,tuple(term),p,shift=-1)
                    self.add_term(out,tuple(term),p,scalar=-1,shift=1)
        if inverse:
            add_vector(out,vector,{1:1,-1:-1})
        return out

    def dot(self, vector, i, sign=1):
        out={}
        for delta,p in vector.items():
            shifted=list(delta);shifted[i-1]+=sign
            out[tuple(shifted)]=p
        return out

    def tau(self, vector, inverse=False):
        if inverse:
            vector=self.dot(vector,1,-1)
            for i in range(1,self.N):vector=self.finite_h(vector,i,True)
        else:
            for i in range(self.N-1,0,-1):vector=self.finite_h(vector,i)
            vector=self.dot(vector,1)
        return vector

    def h(self, vector, i):
        if i:return self.finite_h(vector,i)
        return self.tau(self.finite_h(self.tau(vector,True),self.N-1))

    def b(self, vector, i):
        out=self.h(vector,i)
        add_vector(out,vector,{1:1})
        return out

    def store(self, w, polynomial):
        estimate=256+sum(180+100*len(p) for p in polynomial.values())
        self.cache[w]=polynomial
        self.cache_sizes[w]=estimate
        self.cache_bytes+=estimate
        while self.cache_bytes>self.cache_limit and len(self.cache)>2:
            oldest=next(iter(self.cache))
            if oldest==self.kl.e:
                self.cache.move_to_end(oldest);continue
            path=self.disk/(hashlib.sha256(repr(oldest).encode()).hexdigest()[:24]+'.pickle.z')
            if oldest not in self.files:
                path.write_bytes(zlib.compress(pickle.dumps(self.cache[oldest],protocol=5),1))
                self.files[oldest]=path
            self.cache_bytes-=self.cache_sizes.pop(oldest)
            del self.cache[oldest]

    def canonical(self,w):
        if w in self.cache:
            self.cache.move_to_end(w)
            return self.cache[w]
        if w in self.files:
            polynomial=pickle.loads(zlib.decompress(self.files[w].read_bytes()))
            self.store(w,polynomial)
            return polynomial
        length=self.kl.length(w)
        s=next(s for s in range(self.N) if self.kl.length(self.kl.right(w,s))<length)
        parent=self.kl.right(w,s)
        # The Hecke module determines the exact lower canonical summands.
        parent_basis=self.kl.canonical(parent)
        raw=self.kl.multiply_packed(parent_basis,s,length-1)
        corrections=[(y,p&self.kl.mask) for y,p in raw.items()
                     if y!=w and (length-self.kl.length(y))%2==0 and p&self.kl.mask]
        polynomial=self.b(self.canonical(parent),s)
        for y,c in corrections:
            add_vector(polynomial,self.canonical(y),scale=-c)
        self.store(w,polynomial)
        self.computed+=1
        now=time.monotonic()
        if now-self.last>15:
            print(json.dumps(dict(stage='polynomial',m=self.m,seconds=now-self.start,
                  computed=self.computed,cached=len(self.cache),disk=len(self.files),
                  memory_estimate_mib=self.cache_bytes/1024**2,
                  current_length=length,current_support=len(polynomial))),flush=True)
            self.last=now
        return polynomial

    def row_orbits(self,polynomial):
        groups={};counts={}
        for delta,p in polynomial.items():
            key=(tuple(sorted(delta[:self.m],reverse=True)),delta[self.m],
                 tuple(sorted(delta[self.m+1:],reverse=True)))
            if key in groups:assert groups[key]==p,(key,groups[key],p)
            groups[key]=p;counts[key]=counts.get(key,0)+1
        for (a,k,b),count in counts.items():
            assert count==len(set(itertools.permutations(a)))*len(set(itertools.permutations(b)))
        return [dict(left=a,middle=k,right=b,coefficient=json_poly(p),monomials=counts[(a,k,b)])
                for (a,k,b),p in sorted(groups.items(),reverse=True)]

    def run_case(self,j):
        start=time.monotonic()
        u=family(self.m,j);x=self.kl.inv(u)
        polynomial=self.canonical(x)
        basis=self.kl.canonical(x)
        gap=self.kl.length(x)
        h=self.kl.unpack(basis[self.kl.e],gap)
        result=dict(m=self.m,j=j,N=self.N,u=u,inverse_window=x,D=gap,
                    canonical_support=len(basis),monomial_support=len(polynomial),
                    canonical_B=json_poly(h),mu=h.get(1,0),
                    row_orbits=self.row_orbits(polynomial),
                    all_coefficients_nonnegative=all(c>=0 for p in polynomial.values() for c in p.values()),
                    exponent_range=[min(min(d) for d in polynomial),max(max(d) for d in polynomial)],
                    seconds=time.monotonic()-start)
        path=DATA/f'canonical-polynomial-m{self.m}j{j}.json'
        path.write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps({k:v for k,v in result.items() if k not in ('row_orbits','canonical_B')}),flush=True)
        return result


def verify_small():
    original=json.loads((CODE.parent/'data/canonical-dot-webs.json').read_text())['cases']
    for m in (2,3):
        calc=PolynomialCanonical(m)
        for j in range(1,m+1):
            result=calc.run_case(j)
            expected=next(c for c in original if c['m']==m and c['j']==j)
            def keyed(rows):
                return {(tuple(r['left']),r['middle'],tuple(r['right'])):r['coefficient'] for r in rows}
            assert keyed(result['row_orbits'])==keyed(expected['row_orbits'])
            assert result['canonical_B']==expected['canonical_B']
    print('All m=2,3 complete Bernstein-polynomial comparisons passed.',flush=True)


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--m',type=int,default=4)
    ap.add_argument('--j',type=int)
    ap.add_argument('--cache-mib',type=int,default=256)
    ap.add_argument('--verify-small',action='store_true')
    args=ap.parse_args()
    if args.verify_small:verify_small()
    else:
        calc=PolynomialCanonical(args.m,args.j,cache_mib=args.cache_mib)
        for j in ([args.j] if args.j else range(1,args.m+1)):calc.run_case(j)
