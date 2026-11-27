"""The chart of Section 4: period matrix R(xi), Gram matrix M = R^T R and the squared lengths of (7.2).

    R = [[r1, r1 x, r1 y], [0, r2, r2 z], [0, 0, r3]],   r3 = 1/(r1 r2)                         (4.1)
    q_m     = |R m|^2      = r1^2 (m1 + x m2 + y m3)^2 + r2^2 (m2 + z m3)^2 + r3^2 m3^2
    q*_m    = |R^-T m|^2   = m1^2/r1^2 + (m2 - x m1)^2/r2^2 + r1^2 r2^2 (m3 - z m2 + (x z - y) m1)^2

The functions accept exact rationals or balls for the five shape coordinates xi = (r1, r2, x, y, z).
Symmetric 3x3 matrices are stored as six numbers in the order (11, 22, 33, 12, 13, 23).
"""

from fractions import Fraction

PAIRS = ((0, 0), (1, 1), (2, 2), (0, 1), (0, 2), (1, 2))


def half_offset(f0):
    """The three coordinates of a nonintegral half-lattice offset."""
    f = tuple(Fraction(x) for x in f0)
    if len(f) != 3:
        raise ValueError("f0 must have exactly three coordinates")
    if any(x.denominator not in (1, 2) for x in f) or all(x.denominator == 1 for x in f):
        raise ValueError("f0 must lie in (1/2)Z^3 outside Z^3")
    return f


def real_vector(xi, v):
    """R(xi) v."""
    r1, r2, x, y, z = xi
    return (r1 * (v[0] + x * v[1] + y * v[2]), r2 * (v[1] + z * v[2]), v[2] / (r1 * r2))


def dual_vector(xi, m):
    """R(xi)^-T m."""
    r1, r2, x, y, z = xi
    return (m[0] / r1, (m[1] - x * m[0]) / r2, r1 * r2 * (m[2] - z * m[1] + (x * z - y) * m[0]))


def gram(xi):
    """M = R^T R as (M11, M22, M33, M12, M13, M23)."""
    r1, r2, x, y, z = xi
    s, t = r1 * r1, r2 * r2
    u = 1 / (s * t)
    return (s, s * x * x + t, s * y * y + t * z * z + u, s * x, s * y, s * x * y + t * z)


def gram_inverse(xi):
    """M^-1 = R^-1 R^-T as (N11, N22, N33, N12, N13, N23)."""
    r1, r2, x, y, z = xi
    s, t = r1 * r1, r2 * r2
    w = s * t                      # r3^-2
    h = x * z - y
    return (1 / s + x * x / t + h * h * w, 1 / t + z * z * w, w, -x / t - h * z * w, h * w, -z * w)


def quad(sym, v):
    """v^T S v for a symmetric matrix in the six-number form."""
    return (sym[0] * v[0] * v[0] + sym[1] * v[1] * v[1] + sym[2] * v[2] * v[2]
            + 2 * (sym[3] * v[0] * v[1] + sym[4] * v[0] * v[2] + sym[5] * v[1] * v[2]))


def sym_apply(sym, v):
    """S v for a symmetric matrix in the six-number form."""
    return (sym[0] * v[0] + sym[3] * v[1] + sym[4] * v[2],
            sym[3] * v[0] + sym[1] * v[1] + sym[5] * v[2],
            sym[4] * v[0] + sym[5] * v[1] + sym[2] * v[2])


def full(sym):
    """The 3x3 tuple form of a symmetric matrix given by six numbers."""
    return ((sym[0], sym[3], sym[4]), (sym[3], sym[1], sym[5]), (sym[4], sym[5], sym[2]))


def moments(v):
    """(v1^2, v2^2, v3^2, v1 v2, v1 v3, v2 v3): the rank-one matrix v v^T in the six-number form."""
    return tuple(v[i] * v[j] for i, j in PAIRS)


def contract(sym, other):
    """tr(S T) for two symmetric matrices in the six-number form."""
    return (sym[0] * other[0] + sym[1] * other[1] + sym[2] * other[2]
            + 2 * (sym[3] * other[3] + sym[4] * other[4] + sym[5] * other[5]))


def dot(a, b):
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]
