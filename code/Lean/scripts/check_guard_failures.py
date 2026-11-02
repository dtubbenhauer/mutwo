#!/usr/bin/env python3
"""Negative controls for the audit mechanism, not mathematical proof certificates.

Both temporary Lean files must fail. No project source is mutated and no
new axiom or proof escape is introduced. The first changes an expected
axiom list; the second adds an explicit, unavailable mathematical premise
before the same typed application used by the endpoint audit.
"""
from pathlib import Path
import json
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]

PROBES = {
    'unexpected_axiom': '''import Guralnick.ModelComparisonCounterexample

/-- info: 'Guralnick.ModelComparisonCounterexample.not_absoluteBoundedness'
depends on axioms: [propext, Classical.choice] -/
#guard_msgs (whitespace := lax) in
#print axioms Guralnick.ModelComparisonCounterexample.not_absoluteBoundedness
''',
    'extra_endpoint_premise': '''import Guralnick.ModelComparisonCounterexample

namespace Guralnick.VerificationNegativeControl

def strengthenedEndpoint (T : Hecke.TheoryFamily)
    (W : ∀ m hm, PolynomialWebLiterature (T m hm))
    (I : CoordinateLiteratureTransfer.Inputs T) (_extra : False) :
    ¬Cohomology.AbsoluteBoundedness :=
  ModelComparisonCounterexample.not_absoluteBoundedness T W I

example (T : Hecke.TheoryFamily)
    (W : ∀ m hm, PolynomialWebLiterature (T m hm))
    (I : CoordinateLiteratureTransfer.Inputs T) :
    ¬Cohomology.AbsoluteBoundedness :=
  strengthenedEndpoint T W I

end Guralnick.VerificationNegativeControl
''',
}


def main():
    reports = ROOT / 'reports'
    reports.mkdir(exist_ok=True)
    results = {}
    with tempfile.TemporaryDirectory(prefix='guralnick-audit-negative-') as tmp:
        for name, source in PROBES.items():
            path = Path(tmp) / (name + '.lean')
            path.write_text(source)
            run = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT,
                                 text=True, stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT)
            (reports / f'negative-{name}.txt').write_text(run.stdout)
            # Check that the intended audit mechanism failed, not an import
            # or environment error. The printed endpoint confirms import.
            if name == 'unexpected_axiom':
                expected = ('Docstring' in run.stdout and 'Quot.sound' in run.stdout)
            else:
                expected = ('type mismatch' in run.stdout.lower() and
                            'False →' in run.stdout and 'strengthenedEndpoint' in run.stdout)
            if run.returncode == 0 or not expected:
                raise RuntimeError(f'Negative control {name} did not fail as intended:\n{run.stdout}')
            results[name] = {'rejected': True, 'exit_code': run.returncode}
    (reports / 'negative-audit-controls.json').write_text(json.dumps(results, indent=2)+'\n')
    print('PASS: unexpected axiom output and extra endpoint premise were both rejected.')


if __name__ == '__main__':
    main()
