"""Exact rational helpers (no floating point anywhere in this module)."""

from fractions import Fraction as Fr
from math import lcm, isqrt


def F(x):
    """Coerce int / Fraction / 'p/q' string to Fraction."""
    return x if isinstance(x, Fr) else Fr(x)


def mat(rows):
    return tuple(tuple(F(x) for x in r) for r in rows)


def matmul(A, B):
    n, m, p = len(A), len(B), len(B[0])
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(m)) for j in range(p)) for i in range(n))


def transpose(A):
    return tuple(tuple(A[i][j] for i in range(len(A))) for j in range(len(A[0])))


def det3(A):
    return (A[0][0] * (A[1][1] * A[2][2] - A[1][2] * A[2][1])
            - A[0][1] * (A[1][0] * A[2][2] - A[1][2] * A[2][0])
            + A[0][2] * (A[1][0] * A[2][1] - A[1][1] * A[2][0]))


def inv3(A):
    d = det3(A)
    if d == 0:
        raise ZeroDivisionError("singular matrix")
    C = [[None] * 3 for _ in range(3)]
    for i in range(3):
        for j in range(3):
            r = [x for x in range(3) if x != i]
            c = [x for x in range(3) if x != j]
            minor = A[r[0]][c[0]] * A[r[1]][c[1]] - A[r[0]][c[1]] * A[r[1]][c[0]]
            C[i][j] = (-1) ** (i + j) * minor
    # inverse = adj / det, adj = C^T
    return tuple(tuple(F(C[j][i]) / d for j in range(3)) for i in range(3))


def matvec(A, v):
    return tuple(sum(A[i][k] * v[k] for k in range(len(v))) for i in range(len(A)))


def quad(A, v):
    """v^T A v."""
    return sum(v[i] * A[i][j] * v[j] for i in range(len(v)) for j in range(len(v)))


def common_denominator(values):
    d = 1
    for x in values:
        d = lcm(d, F(x).denominator)
    return d


def integerize(A):
    """Return (D, Ai) with Ai = D*A an integer matrix (tuple of tuples of int)."""
    D = common_denominator(x for r in A for x in r)
    return D, tuple(tuple(int(x * D) for x in r) for r in A)


def isqrt_ceil_frac(q):
    """Smallest integer T >= 0 with T^2 >= q (q a nonnegative Fraction)."""
    q = F(q)
    if q <= 0:
        return 0
    t = isqrt(q.numerator // q.denominator)
    while Fr(t * t) < q:
        t += 1
    return t


# cos(2*pi*x) for rational x is rational exactly when the reduced denominator of x
# lies in {1, 2, 3, 4, 6} (Niven's theorem); these are the only cases we need exactly.
_RATIONAL_COS = {1: {0: Fr(1)},
                 2: {1: Fr(-1)},
                 3: {1: Fr(-1, 2), 2: Fr(-1, 2)},
                 4: {1: Fr(0), 3: Fr(0)},
                 6: {1: Fr(1, 2), 5: Fr(1, 2)}}


def cos2pi_rational(x):
    """cos(2*pi*x) as an exact Fraction if rational, else None."""
    x = F(x) % 1
    q = x.denominator
    if q in _RATIONAL_COS:
        return _RATIONAL_COS[q][x.numerator]
    return None
