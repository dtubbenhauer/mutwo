#!/usr/bin/env python3
"""Independent Python recomputation. This is NOT a Lean-verified KL checker.

The vendored, unchanged research engine computes the m=2,3 spherical
coefficients. For m=2 a second bar-invariance algorithm checks the full
canonical vectors. Output is deliberately marked as experimental data.
"""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import json
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts/vendor'))
from guralnick_candidate_kl import PackedKL, BarKL, endpoint

def main():
    outputs=[]
    for m in (2,3):
        stored=json.loads((ROOT/f'certificates/reference/kl-m{m}.json').read_text())
        calc=PackedKL(2*m,2*m*(m+1)-3)
        bar=BarKL(2*m) if m==2 else None
        for j in range(1,m+1):
            start=time.monotonic()
            _,u,x=endpoint(calc,m,j)
            gap=calc.length(x)
            basis=calc.canonical(x)
            h=calc.unpack(basis[calc.e],gap)
            if bar:
                other=bar.canonical_by_bar(x)
                assert set(other)==set(basis)
                assert all(other[y]==calc.unpack(basis[y],gap-calc.length(y)) for y in basis)
            reference=stored[j-1]
            assert list(u)==reference['u']
            assert h=={int(k):v for k,v in reference['h'].items()}
            outputs.append(dict(m=m,j=j,u=u,inverse=x,gap=gap,h=h,
                mu=h.get(1,0),full_bar_comparison=bar is not None,
                status='experimental; KL algorithm and semantic dictionary not proved in Lean',
                seconds=time.monotonic()-start))
            print(json.dumps(outputs[-1]),flush=True)
    (ROOT/'reports/python-kl-comparison.json').write_text(json.dumps(outputs,indent=2)+'\n')

if __name__=='__main__': main()
