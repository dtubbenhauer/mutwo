#!/usr/bin/env python3
"""Portable bounded-time entrypoint; all calculations use exact integers.

Saved historical data are never overwritten. Default timeout: 300 seconds.
The original modules are imported unchanged, bypassing their RLIMIT_AS CLI.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]


def worker(args):
    from guralnick_candidate_kl import PackedKL, BarKL, endpoint
    from spherical_web import SphericalWeb, family

    output = Path(args.output_dir).resolve()
    output.mkdir(parents=True, exist_ok=True)
    indices = [args.j] if args.j is not None else range(1, args.m + 1)
    maximum = max(indices)
    gap_bound = 2 * maximum * (2 * args.m + 1 - maximum) - 2 * (args.m - maximum) - 3
    if args.engine == 'bernstein':
        import bernstein_canonical as bernstein
        bernstein.DATA = output
        calculator = bernstein.PolynomialCanonical(args.m, maximum, args.cache_mib)
        for j in indices:
            calculator.run_case(j)
        return

    with tempfile.TemporaryDirectory(prefix='guralnick-kl-') as temporary:
        calculator = PackedKL(2 * args.m, gap_bound, cache_mib=args.cache_mib,
                              disk_dir=temporary if args.disk_cache else None)
        independent = BarKL(2 * args.m) if args.verify else None
        sparse = SphericalWeb(2 * args.m + 1) if args.verify else None
        for j in indices:
            started = time.monotonic()
            permutation, u, x = endpoint(calculator, args.m, j)
            assert u == family(args.m, j)
            basis = calculator.canonical(x)
            D = calculator.length(x)
            h = calculator.unpack(basis[calculator.e], D)
            if independent is not None:
                decoded = {y: calculator.unpack(p, D - calculator.length(y))
                           for y, p in basis.items()}
                assert independent.canonical_by_bar(x) == decoded
                assert sparse.canonical(x) == decoded
            P = {(D - d) // 2: c for d, c in h.items()}
            result = dict(m=args.m, j=j, N=2 * args.m + 1, u=u,
                          inverse_window=x, D=D,
                          P_ascending_coefficients=[P.get(i, 0) for i in range(max(P) + 1)],
                          canonical_B={str(k): v for k, v in sorted(h.items())},
                          mu=h.get(1, 0), canonical_support=len(basis),
                          independent_bar_check=bool(independent),
                          separate_sparse_check=bool(sparse),
                          seconds=time.monotonic() - started)
            path = output / f'kl-m{args.m}j{j}.json'
            path.write_text(json.dumps(result, indent=2) + '\n')
            print(json.dumps(result), flush=True)


def main():
    if not __debug__:
        raise SystemExit('Run without -O: the exact algorithms use assertion checks.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--engine', choices=['kl', 'bernstein'], default='kl')
    parser.add_argument('--m', type=int, default=2)
    parser.add_argument('--j', type=int)
    parser.add_argument('--verify', action='store_true', help='Compare whole KL vectors with bar and sparse implementations (m<=3).')
    parser.add_argument('--cache-mib', type=int, default=256)
    parser.add_argument('--disk-cache', action='store_true', help='Use temporary disk cache for the direct KL engine.')
    parser.add_argument('--output-dir', default=str(ROOT / 'results'))
    parser.add_argument('--timeout', type=float, default=300, help='Wall-clock limit in seconds; default 300.')
    parser.add_argument('--worker', action='store_true', help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.m < 2 or (args.j is not None and not 1 <= args.j <= args.m):
        parser.error('Require m>=2 and 1<=j<=m.')
    if args.cache_mib <= 0 or args.timeout <= 0:
        parser.error('Cache and timeout must be positive.')
    if args.verify and (args.m > 3 or args.engine != 'kl'):
        parser.error('This bounded quick-check wrapper supports --verify only for KL at m<=3.')
    if args.disk_cache and args.engine != 'kl':
        parser.error('--disk-cache applies to the direct KL engine only.')
    if Path(args.output_dir).resolve() == (ROOT / 'data').resolve():
        parser.error('Choose a separate output directory; data contains immutable historical records.')
    if args.worker:
        worker(args)
    else:
        command = [sys.executable, str(Path(__file__).resolve()), *sys.argv[1:], '--worker']
        try:
            result = subprocess.run(command, timeout=args.timeout)
            raise SystemExit(result.returncode)
        except subprocess.TimeoutExpired:
            print(f'Stopped at {args.timeout:g} seconds. Only completed case files are results.', file=sys.stderr)
            raise SystemExit(124)


if __name__ == '__main__':
    main()
