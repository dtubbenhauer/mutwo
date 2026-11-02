#!/usr/bin/env python3
"""Check hashes and consistency of saved records; this is not KL recomputation."""
from collections import Counter
import hashlib
import json
from math import factorial, prod
from pathlib import Path
import sys

from guralnick_candidate_kl import AffineKL, endpoint
from spherical_web import family

ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def orbit_size(sequence):
    return factorial(len(sequence)) // prod(factorial(c) for c in Counter(sequence).values())


def main():
    manifest = json.loads((ROOT / 'provenance.json').read_text())
    for entry in manifest['original_files']:
        path = ROOT / entry['packaged_path']
        require(hashlib.sha256(path.read_bytes()).hexdigest() == entry['sha256'], f'Hash mismatch: {path}')
    cases = {}
    for path in sorted((ROOT / 'data').glob('canonical-polynomial-*.json')):
        case = json.loads(path.read_text())
        m, j, N, D = (case[k] for k in ['m', 'j', 'N', 'D'])
        require(N == 2*m+1 and 2 <= m and 1 <= j <= m, str(path))
        calculator = AffineKL(N-1)
        _, u, x = endpoint(calculator, m, j)
        require(list(u) == case['u'] == list(family(m,j)), f'Family: {path}')
        require(list(x) == case['inverse_window'], f'Inverse: {path}')
        require(D == calculator.length(x) == 2*j*(N-j)-2*(m-j)-3, f'Length: {path}')
        h = {int(d): c for d,c in case['canonical_B'].items()}
        require(all(0 < d <= D and (D-d)%2 == 0 and isinstance(c,int) and c>0 for d,c in h.items()), f'Coefficient shape: {path}')
        require(h.get(D) == 1 and case['mu'] == h.get(1,0), f'Coefficient readout: {path}')
        keys = set()
        for row in case['row_orbits']:
            a,b,k = row['left'],row['right'],row['middle']
            require(len(a)==len(b)==m and a==sorted(a,reverse=True) and b==sorted(b,reverse=True), f'Orbit order: {path}')
            require(sum(a)+k+sum(b)==0, f'Winding: {path}')
            key = (tuple(a),k,tuple(b))
            require(key not in keys, f'Duplicate orbit: {path}')
            keys.add(key)
            require(row['monomials']==orbit_size(a)*orbit_size(b), f'Orbit size: {path}')
            require(all(isinstance(c,int) and c>0 for c in row['coefficient'].values()), f'Positive orbit coefficients: {path}')
        require(sum(r['monomials'] for r in case['row_orbits'])==case['monomial_support'], f'Monomial support: {path}')
        cases[m,j] = case
    expected = {(m,j) for m in range(2,6) for j in range(1,m+1)} | {(6,j) for j in range(1,5)}
    require(set(cases)==expected,'Unexpected Bernstein data coverage.')
    aggregate = json.loads((ROOT/'data/aggregate-mu-audit.json').read_text())
    require(len(aggregate['pairs'])==14,'Expected fourteen complete-row direct KL cases.')
    for entry in aggregate['pairs']:
        case = cases[entry['k'],entry['j']]
        D = case['D']
        h = {str(D-2*d): c for d,c in enumerate(entry['P']) if c}
        require(h==case['canonical_B'] and entry['mu']==case['mu'], 'Direct KL/Bernstein disagreement.')
        require(entry['v']==case['u'] and entry['x']==case['inverse_window'] and entry['gap']==D, 'Direct KL endpoint disagreement.')
        require(entry['support']==case['canonical_support'],'Direct KL support disagreement.')
    for entry in json.loads((ROOT/'data/standalone-k3-verified.json').read_text()):
        case=cases[entry['k'],entry['j']]
        h={str(case['D']-2*d):c for d,c in enumerate(entry['P']) if c}
        require(entry['independent_bar_check'] and h==case['canonical_B'],'Historical bar comparison disagreement.')
    diagonal = json.loads((ROOT/'data/n12k6.json').read_text())
    require(diagonal['n']==12 and diagonal['k']==6,'Rank-six metadata.')
    P={int(d):c for d,c in diagonal['P'].items()}
    require(set(P)==set(range(41)) and P[0]==1 and P[40]==diagonal['mu']==6,'Rank-six diagonal degree/readout.')
    require(all(isinstance(c,int) and c>0 for c in P.values()),'Rank-six polynomial coefficients.')
    report = dict(check='saved record integrity and consistency only; no canonical recursion rerun',
                  passed=True, source_hashes_checked=len(manifest['original_files']),
                  bernstein_records=len(cases), complete_rows={str(m):[cases[m,j]['mu'] for j in range(1,m+1)] for m in range(2,6)},
                  partial_m6={str(j):cases[6,j]['mu'] for j in range(1,5)},
                  direct_kl_m6_diagonal=diagonal['mu'], missing_m6=[5],
                  lean_certification=False)
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    if not __debug__:
        raise SystemExit('Run without -O: imported algorithms use assertions.')
    main()
