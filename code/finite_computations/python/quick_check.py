#!/usr/bin/env python3
"""Recompute m=2,3, compare full small canonical vectors and saved output."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    if not __debug__:
        raise SystemExit('Run without -O.')
    reports = ROOT / 'reports'
    reports.mkdir(exist_ok=True)
    check = subprocess.run([sys.executable, str(ROOT/'python/check_saved.py')],
                           text=True, capture_output=True, check=True, timeout=60)
    integrity = json.loads(check.stdout)
    (reports/'saved-data-check.json').write_text(check.stdout)
    checked = []
    old_dot = json.loads((ROOT/'data/canonical-dot-webs.json').read_text())['cases']
    for m in (2,3):
        for engine in ('kl','bernstein'):
            output = reports / f'quick-{engine}-m{m}'
            command = [sys.executable, str(ROOT/'python/run.py'), '--engine', engine,
                       '--m',str(m),'--output-dir',str(output),'--timeout','60']
            if engine=='kl':
                command.append('--verify')
            # Independent working directory tests portable paths and imports.
            with tempfile.TemporaryDirectory(prefix='guralnick-cwd-') as cwd:
                completed = subprocess.run(command, cwd=cwd, text=True,
                                           capture_output=True, check=True, timeout=65)
            (reports/f'quick-{engine}-m{m}.log').write_text(completed.stdout)
        for j in range(1,m+1):
            stored=json.loads((ROOT/f'data/canonical-polynomial-m{m}j{j}.json').read_text())
            fresh=json.loads((reports/f'quick-bernstein-m{m}/canonical-polynomial-m{m}j{j}.json').read_text())
            assert {k:v for k,v in fresh.items() if k!='seconds'}=={k:v for k,v in stored.items() if k!='seconds'}
            kl=json.loads((reports/f'quick-kl-m{m}/kl-m{m}j{j}.json').read_text())
            assert kl['canonical_B']==stored['canonical_B'] and kl['canonical_support']==stored['canonical_support']
            assert kl['independent_bar_check'] and kl['separate_sparse_check']
            dot=next(c for c in old_dot if c['m']==m and c['j']==j)
            def keyed(rows):
                return {(tuple(r['left']),r['middle'],tuple(r['right'])):r['coefficient'] for r in rows}
            assert keyed(fresh['row_orbits'])==keyed(dot['row_orbits'])
            assert fresh['canonical_B']==dot['canonical_B']
            checked.append(dict(m=m,j=j,mu=fresh['mu'],canonical_support=fresh['canonical_support']))
    # Exercise the actual stop path without starting an expensive calculation.
    with tempfile.TemporaryDirectory(prefix='guralnick-timeout-') as output:
        stopped=subprocess.run([sys.executable,str(ROOT/'python/run.py'),'--m','2',
                                '--timeout','0.000001','--output-dir',output],
                               capture_output=True,text=True,timeout=10)
    assert stopped.returncode==124, stopped.stderr
    report=dict(passed=True, saved_data_check=integrity,
                freshly_recomputed_cases=checked,
                checks=['Exact whole canonical vectors agree between packed recursion, triangular bar invariance, and separate sparse Laurent recursion for m=2,3.',
                        'Fresh Bernstein complete outputs agree with historical records, except timing metadata.',
                        'Fresh Bernstein orbit coefficients agree with historical independent monomial-inversion outputs.',
                        'Portable entrypoints execute from unrelated working directories.',
                        'Timeout exits 124 and stops the child process.'],
                not_checked=['No fresh m>=4 canonical computation.',
                             'No independent rank-six diagonal recomputation.',
                             'No Lean certification of the Python algorithms or their output.',
                             'No cohomological transfer is proved by these Python computations.'])
    (reports/'quick-check.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    main()
