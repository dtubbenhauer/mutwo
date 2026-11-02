"""Exact affine type-A KL coefficients for a two-incidence candidate family.

Usage (Python 3, standard library only):
    python guralnick_candidate_kl.py 4          # all j=1,...,4
    python guralnick_candidate_kl.py 4 --j 3    # one endpoint pair
    python guralnick_candidate_kl.py 3 --verify

The finite root system is A_(2k), N=2k+1. Put eta_j=(1^j,0^(N-2j),-1^j).
Let u fix positions outside [j,N-j+1], send j to k+2 and N-j+1 to k,
and map the remaining middle positions increasingly to the remaining values.
The standard affine window used here is v=u*t_(-eta_j), x=v^(-1).
Its length is D=2j(N-j)-2(k-j)-3. With Scott's anti-dominant-wall
convention this same Coxeter element is denoted u*t_(eta_j).

NORMALIZATION
The trivial-induced RIGHT Hecke module has standard basis M_y for minimal
LEFT finite-parabolic cosets and canonical coefficients m[y,x](t):
    m[e,v^-1](t) = t^D * P[w0,v*w0](t^-2).
Thus mu(w0,v*w0)=[t]m[e,v^-1]=[q^((D-1)/2)]P[w0,v*w0].
To match lattice conventions, use periodic basis f_(i+N)=z^-1 f_i;
window i-N*eta_i acts by diag(z^eta_i). The finite parabolic is s1,...,s(2k).

ARITHMETIC
All operations are exact Python integer operations. Polynomial coefficients
are packed in radix 2^(L+2), where L is the largest target length. The
coefficient bound <=2^L and positivity ensure no carries or borrows in the
canonical-product recursion (Luebeck, Lemma 2.8). --verify reconstructs
canonical bases separately from triangular bar invariance; it shares only
affine-window arithmetic and does not use the canonical-product recursion.
This deliberately slow independent check is limited to k<=4.

SCOPE
Complete finite checks give mu=j for 1<=j<=k<=5, and main diagonal values
mu=k for k=6. These computations do not prove a formula for all k or any
representation-theoretic connection. The individual formula mu=j is a
conjectural pattern unless independently proved. No expected mu is imposed
by the algorithm; assertions check its algebraic invariants.

PRIMARY ALGORITHM AND CONVENTION REFERENCES
F. Luebeck, section 2, https://arxiv.org/pdf/1610.07055
L. Scott and N. Xi, https://arxiv.org/pdf/0909.3394
The latter proves the k=j=2 case (in all eligible ranks), not this entire
new two-parameter family.
"""
import argparse
from collections import OrderedDict
from functools import lru_cache
import json
from pathlib import Path
import pickle
import resource
import sys
import time
import zlib

class AffineKL:
    def __init__(self,n):
        self.n=n;self.N=n+1;self.e=tuple(range(1,n+2))
        self.bases={self.e:{self.e:{0:1}}}

    @lru_cache(maxsize=200000)
    def right(self,w,s):
        a=list(w)
        if s==0:a[0],a[-1]=a[-1]-self.N,a[0]+self.N
        else:a[s-1],a[s]=a[s],a[s-1]
        return tuple(a)

    @lru_cache(maxsize=200000)
    def inv(self,w):
        a=[0]*self.N
        for i,v in enumerate(w,1):
            residue=(v-1)%self.N+1
            a[residue-1]=i-(v-residue)
        return tuple(a)

    @lru_cache(maxsize=200000)
    def length(self,w):
        return sum(abs((w[j]-w[i])//self.N)
                   for i in range(self.N) for j in range(i+1,self.N))

    @lru_cache(maxsize=200000)
    def minimal(self,w):
        a=self.inv(w)
        return all(a[i]<a[i+1] for i in range(self.n))

    def element(self,word):
        w=self.e
        for s in word:w=self.right(w,s)
        return w

    @staticmethod
    def addpoly(out,key,p,shift=0,mul=1):
        q=out.setdefault(key,{})
        for d,c in p.items():
            d+=shift
            q[d]=q.get(d,0)+mul*c
            if q[d]==0:del q[d]
        if not q:del out[key]

    def multiply(self,basis,s):
        out={}
        for w,p in basis.items():
            ws=self.right(w,s)
            if self.minimal(ws):
                self.addpoly(out,ws,p)
                self.addpoly(out,w,p,1 if self.length(ws)>self.length(w) else -1)
            else:
                self.addpoly(out,w,p,1)
                self.addpoly(out,w,p,-1)
        return out

    def canonical(self,x):
        if x in self.bases:return self.bases[x]
        assert self.minimal(x)
        lx=self.length(x)
        s=next(s for s in range(self.N) if self.length(self.right(x,s))<lx)
        xp=self.right(x,s)
        out=self.multiply(self.canonical(xp),s)
        assert out[x]=={0:1}
        # By the canonical-product recursion only constant corrections occur.
        corrections=[(y,p.get(0,0)) for y,p in out.items() if y!=x and p.get(0,0)]
        for y,c in corrections:
            assert self.length(y)<lx
            for z,p in self.canonical(y).items():self.addpoly(out,z,p,mul=-c)
        assert out[x]=={0:1}
        for y,p in out.items():
            if y==x:continue
            assert all(d>0 and (d-lx+self.length(y))%2==0 and c>=0 for d,c in p.items())
        self.bases[x]=out
        return out


class PackedKL(AffineKL):
    def __init__(self,n,max_length,cache_mib=512,finite_J=None,disk_dir=None):
        super().__init__(n)
        self.J=tuple(range(1,n+1)) if finite_J is None else tuple(finite_J)
        self.max_length=max_length
        self.bits=max_length+2
        self.B=1<<self.bits
        self.mask=self.B-1
        self.bases=OrderedDict([(self.e,{self.e:1})])
        self.cache_size={self.e:256}
        self.cache_bytes=256
        self.cache_limit=int(cache_mib*1024**2)
        self.started=time.monotonic()
        self.last=self.started
        self.computed=0
        self.evicted=0
        self.largest=1
        self.highest_length=0
        self.disk_dir=Path(disk_dir) if disk_dir else None
        if self.disk_dir:self.disk_dir.mkdir(parents=True,exist_ok=True)
        self.disk={}
        self.disk_loads=0

    def minimal(self,w):
        a=self.inv(w)
        return all(a[s-1]<a[s] for s in self.J)

    @staticmethod
    def add(out,y,p):
        out[y]=out.get(y,0)+p

    def multiply_packed(self,basis,s,old_length):
        out={}
        for w,p in basis.items():
            lw=self.length(w)
            parity=(old_length-lw)%2
            ws=self.right(w,s)
            if self.minimal(ws):
                self.add(out,ws,p)
                if self.length(ws)>lw:
                    self.add(out,w,p<<self.bits if parity else p)
                else:
                    assert parity or not (p&self.mask)
                    self.add(out,w,p if parity else p>>self.bits)
            else:
                assert parity or not (p&self.mask)
                self.add(out,w,(p<<self.bits)+p if parity else p+(p>>self.bits))
        return out

    def store_basis(self,x,out):
        estimate=sys.getsizeof(out)+sum(48+sys.getsizeof(p) for p in out.values())
        self.bases[x]=out
        self.cache_size[x]=estimate
        self.cache_bytes+=estimate
        while self.cache_bytes>self.cache_limit and len(self.bases)>2:
            oldest=next(iter(self.bases))
            if oldest==self.e:
                self.bases.move_to_end(oldest)
                continue
            if self.disk_dir and oldest not in self.disk:
                path=self.disk_dir/f'{len(self.disk):08d}.pickle.z'
                data=pickle.dumps((oldest,self.bases[oldest]),protocol=5)
                path.write_bytes(zlib.compress(data,1))
                self.disk[oldest]=path
            self.cache_bytes-=self.cache_size.pop(oldest)
            del self.bases[oldest]
            self.evicted+=1

    def canonical(self,x):
        if x in self.bases:
            self.bases.move_to_end(x)
            return self.bases[x]
        if x in self.disk:
            saved_x,out=pickle.loads(zlib.decompress(self.disk[x].read_bytes()))
            assert saved_x==x
            self.disk_loads+=1
            self.store_basis(x,out)
            return out
        assert self.minimal(x)
        lx=self.length(x)
        assert lx<=self.max_length
        s=next(s for s in range(self.N) if self.length(self.right(x,s))<lx)
        xp=self.right(x,s)
        out=self.multiply_packed(self.canonical(xp),s,lx-1)
        assert out[x]==1
        corrections=[(y,p&self.mask) for y,p in out.items()
                     if y!=x and (lx-self.length(y))%2==0 and p&self.mask]
        for y,c in corrections:
            assert self.length(y)<lx
            for z,p in self.canonical(y).items():
                out[z]-=c*p
                assert out[z]>=0
                if not out[z]:del out[z]
        assert out[x]==1
        for y,p in out.items():
            if y!=x and (lx-self.length(y))%2==0:
                assert not (p&self.mask)
        self.store_basis(x,out)
        self.computed+=1
        self.largest=max(self.largest,len(out))
        self.highest_length=max(self.highest_length,lx)
        now=time.monotonic()
        if now-self.last>15:
            self.last=now
            print(json.dumps(dict(seconds=now-self.started,computed=self.computed,
                                  cached=len(self.bases),evicted=self.evicted,
                                  cache_mib=self.cache_bytes/1024**2,
                                  largest_support=self.largest,max_length=self.highest_length,
                                  disk_bases=len(self.disk),disk_loads=self.disk_loads,
                                  maxrss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)),flush=True)
        return out

    def unpack(self,p,gap):
        result={}
        degree=gap%2
        while p:
            c=p&self.mask
            assert c<(1<<(self.max_length+1))
            if c:result[degree]=c
            p>>=self.bits
            degree+=2
        return result


def add(p,q,mul=1,shift=0):
    for d,c in q.items():
        d+=shift
        p[d]=p.get(d,0)+mul*c
        if not p[d]:del p[d]


def product(p,q):
    result={}
    for d,c in p.items():add(result,q,c,d)
    return result


class BarKL(AffineKL):
    @lru_cache(None)
    def bar_standard(self,z):
        if z==self.e:return {z:{0:1}}
        lz=self.length(z)
        s=next(s for s in range(self.N) if self.length(self.right(z,s))<lz)
        zp=self.right(z,s)
        result={}
        for y,p in self.bar_standard(zp).items():
            ys=self.right(y,s)
            if self.minimal(ys):
                add(result.setdefault(ys,{}),p)
                if self.length(ys)>self.length(y):
                    target=result.setdefault(y,{})
                    add(target,p,shift=1)
                    add(target,p,mul=-1,shift=-1)
            else:
                add(result.setdefault(y,{}),p,shift=1)
        return {y:p for y,p in result.items() if p}

    def canonical_by_bar(self,x):
        residual={y:dict(p) for y,p in self.bar_standard(x).items() if y!=x}
        assert self.bar_standard(x)[x]=={0:1}
        answer={x:{0:1}}
        for y in sorted(residual,key=self.length,reverse=True):
            rhs=residual[y]
            positive={d:c for d,c in rhs.items() if d>0}
            reflected={-d:c for d,c in positive.items()}
            check=dict(positive)
            add(check,reflected,mul=-1)
            assert rhs==check, (y,rhs,check)
            if not positive:continue
            assert all(c>=0 for c in positive.values())
            answer[y]=positive
            for z,p in self.bar_standard(y).items():
                if z!=y:add(residual.setdefault(z,{}),product(reflected,p))
        return answer


def compose(w,v):
    N=len(w)
    return tuple(w[(j-1)%N]+((j-1)//N)*N for j in v)


def endpoint(a,k,j):
    N=a.N
    assert 1<=j<=k and N==2*k+1
    r=N-j+1
    eta=[1]*j+[0]*(N-2*j)+[-1]*j
    translation=tuple(i+1-N*eta[i] for i in range(N))
    u=list(a.e)
    u[j-1],u[r-1]=k+2,k
    middle=iter(i for i in range(j,r+1) if i not in (k,k+2))
    for index in range(j+1,r):u[index-1]=next(middle)
    v=compose(tuple(u),translation)
    x=a.inv(v)
    assert a.minimal(x)
    assert a.length(x)==2*j*(N-j)-2*(k-j)-3
    return tuple(u),v,x


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('k',type=int)
    parser.add_argument('--j',type=int)
    parser.add_argument('--verify',action='store_true')
    parser.add_argument('--cache-mib',type=int,default=256)
    parser.add_argument('--memory-gib',type=float,default=2)
    parser.add_argument('--disk-cache-dir')
    parser.add_argument('--json-output')
    args=parser.parse_args()
    if args.k<2:parser.error('k must be at least 2')
    if args.j is not None and not 1<=args.j<=args.k:parser.error('require 1<=j<=k')
    if args.verify and args.k>4:parser.error('--verify is intentionally limited to k<=4')
    limit=int(args.memory_gib*1024**3)
    resource.setrlimit(resource.RLIMIT_AS,(limit,limit))
    k=args.k
    indices=[args.j] if args.j is not None else list(range(1,k+1))
    max_length=max(2*j*(2*k+1-j)-2*(k-j)-3 for j in indices)
    a=PackedKL(2*k,max_length,cache_mib=args.cache_mib,disk_dir=args.disk_cache_dir)
    check=BarKL(2*k) if args.verify else None
    outputs=[]
    for j in indices:
        started=time.monotonic()
        u,v,x=endpoint(a,k,j)
        gap=a.length(x)
        basis=a.canonical(x)
        polynomial=a.unpack(basis[a.e],gap)
        if check:
            independently=check.canonical_by_bar(x)
            assert set(independently)==set(basis)
            for y,poly in independently.items():
                assert poly==a.unpack(basis[y],gap-a.length(y))
        P={(gap-d)//2:c for d,c in polynomial.items()}
        output=dict(k=k,j=j,N=2*k+1,u=u,v=v,x=x,gap=gap,
                    P=[P.get(i,0) for i in range(max(P)+1)],
                    mu=polynomial.get(1,0),support=len(basis),
                    independent_bar_check=bool(check),seconds=time.monotonic()-started)
        outputs.append(output)
        print(json.dumps(output),flush=True)
    if args.j is None:
        print(json.dumps(dict(k=k,sum_mu=sum(p['mu'] for p in outputs),
                              triangular_comparison=k*(k+1)//2)),flush=True)
    if args.json_output:Path(args.json_output).write_text(json.dumps(outputs,indent=2)+'\n')


if __name__=='__main__':
    main()
