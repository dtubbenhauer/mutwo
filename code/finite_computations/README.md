# Finite affine KL computations

This folder contains the exact Python programs and saved numerical results
discussed alongside the Lean formalization. It is independent of the Lean
build. The Python calculations are **not Lean-certified certificates** and
do not establish the representation-theoretic transfer to first cohomology.

## What the records contain

| Family parameters | Saved result | Coverage |
|---|---|---|
| `m=2,3,4,5`, every `1<=j<=m` | `mu=j`, full normalized source polynomials and complete Bernstein orbit expansions | Complete rows |
| `m=6`, `j=1,2,3,4` | `mu=1,2,3,4`, respectively, with the same full outputs | Partial row |
| `m=j=6` | `mu=6`, full degree-40 ordinary KL polynomial | Direct KL computation only |

No completed `m=6,j=5` calculation is included. There is no complete sixth
row here, and no general proof of the individual formula `mu_(j;m)=j`.
The uniform row-sum theorem in Lean is separate from these finite examples.

The saved diagonal `m=6` calculation took about 551.5 seconds (9.2 minutes).
The Bernstein `m=6,j=4` record took about 244.5 seconds. These are historical
timings from different computations and cache conditions, not controlled
benchmarks. No calculation of this size was rerun to assemble this folder.

## Conventions and endpoint

The affine period is `N=2m+1`; the finite root rank is `2m`. The code's
parameter `k` is the paper's `m`. In the original KL module the window called
`v` is the paper's increasing window `u_(j;m)`; its local variable `u` is a
different finite permutation. The wrapper instead names the increasing
window `u` explicitly. The canonical right spherical module index is
`x=u^(-1)`, with minimal **left** finite-parabolic representatives. The
trivial source is preserved through the spherical wall rule.

The normalized source coefficient is

```
D = 2*j*(N-j) - 2*(m-j) - 3
h(v) = v^D P_(w0,u*w0)(v^(-2))
mu = coefficient of v^1 in h(v).
```

`canonical_B` stores `h` as degree-to-integer JSON entries. `P` is stored
as ascending coefficients in `aggregate-mu-audit.json`, but as a
degree-to-coefficient dictionary in `n12k6.json`. The latter has `n=12`,
`k=6`: thus `N=13`, `D=81`, and the critical ordinary KL degree is 40.

Bernstein exponent tuples describe the commuting winding variables
`X_1,...,X_N`; powers of the Hecke parameter `v` occur in their coefficients.
They are different gradings. In particular, the coefficient of the zero
Bernstein monomial is not, in general, `canonical_B`. That field is read
from the spherical standard coefficient at the identity.

## Files and trust

- `python/guralnick_candidate_kl.py`: unchanged exact packed-integer
  canonical-product recursion, plus an independently implemented
  triangular bar-invariance algorithm.
- `python/bernstein_canonical.py`: unchanged Bernstein polynomial action
  and canonical transport. Its correction coefficients come from the
  packed KL recursion, so these two implementations are not independent
  checks of each other's canonical corrections.
- `python/spherical_web.py`: unchanged separate sparse Laurent-polynomial
  implementation, including the explicit sorted-window family.
- `python/run.py`: portable entrypoint with a time limit and separate
  generated-output directory. It avoids the original CLI's `RLIMIT_AS`
  call, which is rejected on macOS.
- `python/check_saved.py`: checks source/data hashes, endpoints, lengths,
  polynomial normalization, orbit multiplicities and agreement of the
  saved direct KL and Bernstein records. **It does not rerun canonical
  recursion or prove that arbitrary stored coefficients are KL values.**
- `python/quick_check.py`: fresh small calculations and comparisons,
  documented below.
- `data/canonical-polynomial-m*j*.json`: 18 historical Bernstein records.
- `data/aggregate-mu-audit.json`: the 14 direct KL cases for complete rows
  `m=2,...,5`.
- `data/standalone-k3-verified.json`: historical full-vector bar checks
  for all three cases at `m=3`.
- `data/n12k6.json`: saved direct KL diagonal at `m=6`.
- `data/canonical-dot-webs.json`: historical independent monomial-inversion
  outputs for the small Bernstein comparisons. They are reference data;
  that separate generator is not included or rerun here.
- `provenance.json`: original workspace paths and SHA-256 hashes for the
  unchanged code and data copies. Hashes record provenance, not correctness.
- `reports/quick-check.json`: checks actually run for this release, with
  scope and limitations. The companion JSONs/logs are their fresh outputs.

The packed arithmetic uses the mathematical positivity/coefficient bound
described in its module docstring. This bound and correctness of the Python
implementation have not themselves been proved in Lean. The original
module documents its algorithm and convention references to Lübeck and
Scott–Xi. These computations make no further cohomological claim.

## Quick verification

Python 3.9 or newer on macOS or Linux is sufficient; only the standard
library is used. Do not use `python -O`, since the original algorithms use
assertions to check invariants. From this folder:

```sh
python3 python/check_saved.py
python3 python/quick_check.py
```

`quick_check.py` recalculates every case at `m=2,3`, compares the **whole**
canonical vectors from the packed, triangular-bar and separate sparse
implementations, recomputes the Bernstein outputs and compares them with
the saved records. It also compares with the saved monomial-inversion
outputs, checks execution from an unrelated working directory and exercises
the timeout path. Each calculation subprocess has a 60-second limit.
This suite completed in seconds during packaging. It does not freshly
recompute the larger examples.

## Reproducing a row or individual case

```sh
python3 python/run.py --m 3 --verify
python3 python/run.py --engine bernstein --m 3
python3 python/run.py --m 5 --j 5
python3 python/run.py --engine bernstein --m 5
```

The wrapper defaults to **300 seconds for the entire invocation**, writes
only completed cases to `results/`, and exits with status 124 if it reaches
the limit. Use `--output-dir PATH` for another location. It never writes
over the saved `data/` records. All commands also work with an absolute
script path from another directory.

For the historical `m=6` diagonal, this bounded command may stop before
completion; it is supplied for reproducibility, not run by the quick suite:

```sh
python3 python/run.py --m 6 --j 6 --disk-cache
```

Only if a longer computation is explicitly wanted, increase `--timeout`
(for example `--timeout 900`). Temporary disk caches are used only within
an invocation and normally cleaned up at exit. A forced timeout may leave
a temporary cache directory; it is disposable. `--cache-mib` controls the
algorithm's approximate cache budget, not the process's total memory.

Use the wrapper rather than the copied original CLIs: the original
Bernstein CLI writes to its adjacent `data/` directory, while the original
direct KL CLI attempts to impose a process address-space limit.
