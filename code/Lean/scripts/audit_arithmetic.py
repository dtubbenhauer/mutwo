#!/usr/bin/env python3
"""Independent finite arithmetic audit of the manuscript's web formulas.

EXPERIMENTAL: these Python checks are not Lean proofs, and they do not
compute or certify a Kazhdan--Lusztig polynomial. No project computation
engine is imported. The periodic matrix length sum and the four count
degrees are calculated independently of the closed-form length/exclusion
polynomials being checked. Gaussian polynomials use their elementary
recurrence with integer coefficient lists.

Run from any working directory. Output: reports/audit-arithmetic.json.
Do not run with Python -O: assertions are part of the checks.
"""

from functools import lru_cache
from hashlib import sha256
from itertools import product
from math import comb
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]


def gaussian_degree(n, k):
    return k * (n - k) if n >= 0 and 0 <= k <= n else None


def integer_degree(n):
    return n - 1 if n > 0 else None


def difference_degree(n, k):
    assert n >= k >= 0
    return n - 1 if n > k else None


def product_degree(*degrees):
    return sum(degrees) if all(d is not None for d in degrees) else None


def periodic_matrix_length(matrix):
    """Evaluate the manuscript's periodic dimension sum, not its formula C.

    The displayed columns are 1-period, 1, 1+period. Only the current
    and predecessor row periods can contribute to j<h with k<=i.
    """
    period = len(matrix)
    columns = [1 - period, 1, 1 + period]
    degree = 0
    for i in range(period):
        for jj, j in enumerate(columns):
            for k in range(-period, i + 1):
                row_period, kk = divmod(k, period)
                for hh, h in enumerate(columns):
                    if j < h + row_period * period:
                        degree += matrix[i][jj] * matrix[kk][hh]
    return degree


def aggregate_audit(max_m=20):
    feasible = nonzero = 0
    per_rank = []
    allowed = {
        (0, 0, 0, 1), (0, 1, 0, 0), (0, 1, 0, 1),
        (0, 0, 1, 1), (1, 0, 0, 1), (1, 1, 0, 1),
    }
    for m in range(2, max_m + 1):
        start_feasible, start_nonzero = feasible, nonzero
        n, total_degree = 2 * m + 1, 2 * m * m + 2 * m - 3
        for r in range(m + 1):
            ell = m - r
            for a, s, (beta, delta) in product(
                range(r + 1), range(r + 1), [(0, 0), (0, 1), (1, 1)]
            ):
                matrix = [
                    [a, ell + s - a, r - s],
                    [beta, delta - beta, 1 - delta],
                    [r - a - beta, ell + 1 - s - delta + a + beta, s + delta - 1],
                ]
                if min(sum(matrix, [])) < 0:
                    continue
                feasible += 1
                b, c, z = a + beta, ell + s, s + delta - 1
                codimension = (
                    s * (ell + s) + a * (ell + a - s + 1)
                    + beta * (ell + a + beta) + (delta - beta) * z
                )
                gap = periodic_matrix_length(matrix)
                assert gap == 2 * r * (n - r) - codimension, (m, r, matrix)
                terms = []
                for epsilon, eta in product(range(2), repeat=2):
                    line = integer_degree(a) if epsilon == 0 else difference_degree(c, a)
                    hyperplane = integer_degree(z) if eta == 0 else difference_degree(ell + b, z)
                    degree = product_degree(
                        line, hyperplane,
                        gaussian_degree(n - 2 * r - epsilon - eta, m - r - epsilon),
                        integer_degree(m + 1 - r - eta),
                    )
                    if degree is not None:
                        terms.append(degree)
                if not terms:
                    continue
                nonzero += 1
                excess = 2 * max(terms) - (total_degree - gap)
                if excess >= 0:
                    assert (
                        ell >= 1 and (a, s, beta, delta) in allowed
                    ) or (
                        ell == 0 and (a, s, beta, delta) == (1, 1, 0, 1)
                    ), (m, r, matrix, excess)
            
        per_rank.append({
            "m": m, "feasible": feasible - start_feasible,
            "nonzero_counts": nonzero - start_nonzero,
        })
    return {
        "range_m": [2, max_m], "feasible_matrices": feasible,
        "nonzero_counts": nonzero, "per_rank": per_rank,
        "checked": ["periodic length identity", "six-position nonnegative-excess exclusion"],
    }


def one_line_audit(max_n=16):
    feasible = parameter_triples = 0
    for n_total in range(3, max_n + 1):
        for j in range(1, (n_total - 1) // 2 + 1):
            for f in range(j, n_total - j + 1):
                parameter_triples += 1
                leading = []
                for r in range(j + 1):
                    n, s, d = n_total - 2 * r, j - r, f - r
                    for a, b in product(range(r + 1), repeat=2):
                        matrix = [[a, d + b - a, r - b], [r - a, n - d - b + a, b]]
                        if min(sum(matrix, [])) < 0:
                            continue
                        feasible += 1
                        c = d + b
                        codimension = b * (d + b) + a * (n - d + a - b)
                        gap = periodic_matrix_length(matrix)
                        assert gap == 2 * r * (n_total - r) - codimension
                        exponent = (2 * j - 1) * (n_total - j) + f - 1
                        terms = [
                            product_degree(integer_degree(a), gaussian_degree(n, s)),
                            product_degree(difference_degree(c, a), gaussian_degree(n - 1, s - 1)),
                        ]
                        terms = [x for x in terms if x is not None]
                        if not terms:
                            continue
                        excess = 2 * max(terms) - (exponent - gap)
                        assert excess <= 0, (n_total, j, f, r, a, b, excess)
                        if excess == 0:
                            leading.append((r, a, b))
                expected = (j, 1, 0) if f > j else (j, 1, 1)
                assert leading == [expected], (n_total, j, f, leading, expected)
    return {
        "range_N": [3, max_n], "parameter_triples": parameter_triples,
        "feasible_matrices": feasible,
        "checked": ["periodic length identity", "nonpositive degree excess", "unique degree-zero index"],
    }


def poly_add(a, b, sign=1):
    result = a + [0] * max(0, len(b) - len(a))
    for i, x in enumerate(b):
        result[i] += sign * x
    while result and result[-1] == 0:
        result.pop()
    return result


def poly_mul(a, b):
    if not a or not b:
        return []
    result = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i + j] += x * y
    return result


def shift(a, exponent):
    assert exponent >= 0
    return [0] * exponent + a if a else []


@lru_cache(None)
def gaussian(n, k):
    if k < 0 or k > n:
        return []
    if k == 0:
        return [1]
    return poly_add(gaussian(n - 1, k), shift(gaussian(n - 1, k - 1), n - k))


def correction_half(ell):
    result = []
    for t in range(ell - 1):
        result = poly_add(result, shift([comb(t + 3, 3)], t))
        result = poly_add(result, shift([comb(t + 3, 3)], 2 * ell - 3 - t))
    return result


def gaussian_audit(max_m=16):
    rows = []
    for m in range(2, max_m + 1):
        raw = poly_mul(poly_mul(poly_mul([1] * m, [1] * m), [1] * m), gaussian(2 * m - 1, m - 1))
        result = raw
        for r in range(m - 1):
            ell = m - r
            ballot = poly_add(
                gaussian(2 * m + 1, r),
                shift(gaussian(2 * m + 1, r - 1), 2 * m + 2 - 2 * r), -1,
            )
            result = poly_add(result, poly_mul(shift(correction_half(ell), ell * ell), ballot), -1)
        expected_degree = m * m + m - 2
        assert len(result) == expected_degree + 1, (m, len(result) - 1)
        assert result[expected_degree] == comb(m + 1, 2), (m, result[-1])
        rows.append({"m": m, "degree": expected_degree, "leading_coefficient": result[-1]})
    return {"range_m": [2, max_m], "rows": rows}


def main():
    if not __debug__:
        raise RuntimeError("Run without Python -O: assertions are required.")
    report = {
        "status": "experimental finite Python checks; not Lean verified; not KL certificates",
        "source_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "aggregate": aggregate_audit(),
        "one_line": one_line_audit(),
        "gaussian_cancellation": gaussian_audit(),
    }
    output = ROOT / "reports/audit-arithmetic.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({
        "status": report["status"],
        "aggregate_matrices": report["aggregate"]["feasible_matrices"],
        "one_line_matrices": report["one_line"]["feasible_matrices"],
        "gaussian_rows": len(report["gaussian_cancellation"]["rows"]),
        "output": str(output),
    }))


if __name__ == "__main__":
    main()
