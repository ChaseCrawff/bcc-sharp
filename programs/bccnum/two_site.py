"""True two-site Coulomb Ewald series and eight-variable interval certificates.

The mathematical bounds and their scope are those of Sections 2 to 4 of the paper.  Period lattices have covolume one here; multiplying
by a_c=(8*pi/3)^(1/3) gives volume 4*pi/3 per particle.  The full offset is retained.
"""

from fractions import Fraction as F
import itertools
import math

import numpy as np
from flint import arb

from .exact import det3, inv3, mat, matmul, transpose

NV = 8


def av(x):
    return arb(x.numerator) / x.denominator if isinstance(x, F) else arb(x)


def exact_index2(name):
    """All seven kernels of nonzero characters of Lambda/2Lambda, exactly.

    The basis search is finite and only proposes bases: exact determinant two
    and parity checks prove each returned basis generates the entire kernel.
    """
    h = F(1, 2)
    B = mat([[-h, h, h], [h, -h, h], [h, h, -h]] if name == "bcc" else
            [[0, h, h], [h, 0, h], [h, h, 0]])
    out = []
    for c in itertools.product((0, 1), repeat=3):
        if not any(c):
            continue
        cand = [m for m in itertools.product(range(-2, 3), repeat=3)
                if any(m) and sum(c[j] * m[j] for j in range(3)) % 2 == 0]
        def norm2(m):
            return sum(sum(B[i][j] * m[j] for j in range(3)) ** 2 for i in range(3))
        cand.sort(key=lambda m: (norm2(m), m))
        U = next(mat(transpose(t)) for t in itertools.combinations(cand[:40], 3)
                 if abs(det3(mat(transpose(t)))) == 2)
        if det3(U) < 0:
            U = tuple(tuple(-x if j == 0 else x for j, x in enumerate(row)) for row in U)
        pivot = next(j for j in range(3) if c[j])
        tau = tuple(F(int(j == pivot)) for j in range(3))
        Ui = inv3(U)
        f = tuple(sum(Ui[i][j] * tau[j] for j in range(3)) for i in range(3))
        f = tuple(x - math.floor(x + F(1, 2)) for x in f)
        assert det3(U) == 2
        assert all(sum(c[i] * U[i][j] for i in range(3)) % 2 == 0 for j in range(3))
        assert all((2 * x).denominator == 1 for x in f) and any(x.denominator == 2 for x in f)
        out.append({"name": name, "character": c, "primitive": B, "U": U,
                    "period": matmul(B, U), "offset": f})
    return out


def symmetry_classes(name):
    """Exact signed-permutation witnesses for all character equivalences."""
    rows = exact_index2(name)
    B, Bi = rows[0]["primitive"], inv3(rows[0]["primitive"])
    actions = []
    for p in itertools.permutations(range(3)):
        for s in itertools.product((-1, 1), repeat=3):
            O = mat([[s[i] if j == p[i] else 0 for j in range(3)] for i in range(3)])
            T = matmul(matmul(Bi, O), B)
            assert all(x.denominator == 1 for row in T for x in row)
            assert abs(det3(T)) == 1
            actions.append((O, T))
    remaining = {r["character"] for r in rows}
    classes = []
    while remaining:
        c = min(remaining)
        witnesses = {}
        for O, T in actions:
            d = tuple(int(sum(T[j][i] * c[j] for j in range(3))) % 2 for i in range(3))
            witnesses.setdefault(d, {"orthogonal_signed_permutation": O, "primitive_action": T})
        assert set(witnesses) <= {r["character"] for r in rows}
        remaining -= set(witnesses)
        classes.append({"representative": c, "members": sorted(witnesses),
                        "witnesses": [{"character": d, **witnesses[d]} for d in sorted(witnesses)]})
    return rows, classes


def float_period(row):
    B = np.array(row["period"], dtype=float)
    return B * (2 ** (1 / 3) if row["name"] == "fcc" else 1.0)


def irreps_float():
    E = [np.diag([1, -1, 0]) / math.sqrt(2), np.diag([1, 1, -2]) / math.sqrt(6)]
    for i, j in ((0, 1), (0, 2), (1, 2)):
        M = np.zeros((3, 3)); M[i, j] = M[j, i] = 1 / math.sqrt(2); E.append(M)
    return np.array(E)


def float_configuration(row, w):
    S = np.einsum("k,kij->ij", np.asarray(w[:5]), irreps_float())
    A = np.eye(3) + S
    A /= np.linalg.det(A) ** (1 / 3)
    B = float_period(row)
    f = np.array(row["offset"], float) + np.linalg.solve(B, np.asarray(w[5:]))
    return A @ B, np.array([[0, 0, 0], f])


class Jet:
    """Dense second-order arb automatic differentiation, eight variables."""
    __slots__ = ("v", "g", "h")

    def __init__(self, v, g=None, h=None):
        self.v = av(v)
        self.g = [arb(0)] * NV if g is None else g
        self.h = [[arb(0)] * NV for _ in range(NV)] if h is None else h

    @classmethod
    def var(cls, v, i):
        g = [arb(0)] * NV; g[i] = arb(1)
        return cls(v, g)

    def __add__(self, b):
        if not isinstance(b, Jet):
            return Jet(self.v + av(b), self.g, self.h)
        return Jet(self.v + b.v, [x + y for x, y in zip(self.g, b.g)],
                   [[x + y for x, y in zip(a, bb)] for a, bb in zip(self.h, b.h)])
    __radd__ = __add__

    def __neg__(self):
        return self * -1

    def __sub__(self, b):
        return self + (-b)

    def __rsub__(self, b):
        return -self + b

    def __mul__(self, b):
        if not isinstance(b, Jet):
            b = av(b)
            return Jet(self.v * b, [x * b for x in self.g], [[x * b for x in r] for r in self.h])
        return Jet(self.v * b.v, [self.v * b.g[i] + b.v * self.g[i] for i in range(NV)],
                   [[self.v * b.h[i][j] + b.v * self.h[i][j] + self.g[i] * b.g[j] + self.g[j] * b.g[i]
                     for j in range(NV)] for i in range(NV)])
    __rmul__ = __mul__

    def apply(self, v, g, h):
        return Jet(v, [g * x for x in self.g],
                   [[h * self.g[i] * self.g[j] + g * self.h[i][j] for j in range(NV)] for i in range(NV)])

    def pow(self, p):
        p = av(p)
        return self.apply(self.v ** p, p * self.v ** (p - 1), p * (p - 1) * self.v ** (p - 2))

    def cos(self):
        return self.apply(self.v.cos(), -self.v.sin(), -self.v.cos())


def mmul(A, B):
    return [[sum((A[i][k] * B[k][j] for k in range(len(B))), Jet(0))
             for j in range(len(B[0]))] for i in range(len(A))]


def trans(A):
    return [list(r) for r in zip(*A)]


def det(A):
    return A[0][0] * (A[1][1] * A[2][2] - A[1][2] * A[2][1]) - A[0][1] * (A[1][0] * A[2][2] - A[1][2] * A[2][0]) + A[0][2] * (A[1][0] * A[2][1] - A[1][1] * A[2][0])


def adj(A):
    return [[A[(j + 1) % 3][(i + 1) % 3] * A[(j + 2) % 3][(i + 2) % 3] -
             A[(j + 1) % 3][(i + 2) % 3] * A[(j + 2) % 3][(i + 1) % 3]
             for j in range(3)] for i in range(3)]


def linear_combination(items):
    items = [(a, b) for a, b in items if b]
    return Jet(sum((a.v * b for a, b in items), arb(0)),
               [sum((a.g[i] * b for a, b in items), arb(0)) for i in range(NV)],
               [[sum((a.h[i][j] * b for a, b in items), arb(0)) for j in range(NV)] for i in range(NV)])


def qjet(M, m):
    return linear_combination([(M[i][i], m[i] ** 2) for i in range(len(m))] +
                              [(M[i][j], 2 * m[i] * m[j]) for i in range(len(m)) for j in range(i)])


def gvalues(x, a, order=2):
    ex = (-x).exp()
    val = ex / x if a == 1 else (arb.pi() / x).sqrt() * x.sqrt().erfc()
    out = [val]
    a = av(a)
    for _ in range(order):
        val = (ex + a * val) / x; a += 1; out.append(val)
    return out


def gj(Q, a):
    pi = arb.pi()
    g = gvalues(pi * Q.v, a)
    return Q.apply(g[0], -pi * g[1], pi * pi * g[2])


def upper(x):
    return arb(x.upper())


def lower(x):
    return arb(x.lower())


def sq(x):
    # arb.pow with a zero-crossing ball can return nan in python-flint 0.9.0.
    # Multiplication is an enclosure even when its lower end is negative.
    return x * x


def norm_upper(xs):
    return upper(upper(sum((sq(x) for x in xs), arb(0))).sqrt())


def ubmax(xs):
    """Maximum of exact upper endpoints, with no float comparison."""
    vals = [upper(x) for x in xs]
    if not vals or not all(x.is_finite() for x in vals):
        raise ArithmeticError("empty or nonfinite upper-bound maximum")
    answer = vals[0]
    for x in vals[1:]:
        if x > answer:
            answer = x
    return answer


def deriv_norms(M):
    """Upper Frobenius norms of the first and second matrix derivatives in every jet coordinate."""
    coordinates = range(len(M[0][0].g))
    K1 = ubmax(norm_upper(x.g[i] for r in M for x in r) for i in coordinates)
    K2 = ubmax(norm_upper(x.h[i][j] for r in M for x in r)
               for i in coordinates for j in coordinates)
    return K1, K2


def gaussian_poly_sum(c, coeffs, n0, extra=24):
    """Upper bound sum_{n>n0} exp(-c n^2) sum_k coeff[k] n^k.

    All coefficients nonnegative; degree at most four.  The final ratio is
    monotone decreasing, so its geometric tail bounds every remaining term.
    """
    assert c > 0 and all(a >= 0 for a in coeffs)
    def term(n):
        return (-c * n * n).exp() * sum((a * n ** k for k, a in enumerate(coeffs)), arb(0))
    N = n0 + extra
    ratio = (arb(N + 1) / N) ** (len(coeffs) - 1) * (-c * (2 * N + 1)).exp()
    if not ratio < 1:
        raise ValueError("tail ratio not below one")
    return upper(sum((term(n) for n in range(n0 + 1, N + 1)), arb(0)) + term(N) * ratio / (1 - ratio))


def family_tail(M, inv_trace, n0, shift=0, phase_g=0, phase_h=0, reciprocal=False):
    """Uniform value, gradient and entrywise Hessian tail bounds.

    M is 3x3 (unshifted) or the augmented 4x4 cross-distance matrix.
    inv_trace bounds the inverse trace of the underlying positive 3x3 Gram.
    shift bounds max |fractional offset|, used only in the distance lower bound.
    phase_g/h bound the derivative norm of the fractional offset times 2*pi*sqrt3.
    """
    mu = lower(1 / inv_trace)
    theta = lower(1 - av(shift) / (n0 + 1))
    if not (mu > 0 and theta > 0):
        raise ValueError("nonpositive tail spectral/shift bound")
    c = lower(arb.pi() * mu * theta ** 2)
    if not c * (n0 + 1) ** 2 >= 1:
        raise ValueError("tail begins before pi Q >= 1")
    K1, K2 = deriv_norms(M)
    pi, P, P2 = arb.pi(), av(phase_g), av(phase_h)
    z = arb(0)
    if reciprocal:
        v = [52 / c]
        g = [z, 130 * P / c, 1040 * pi * K1 / c]
        h = [z, 130 * P2 / c, 130 * (8 * pi * K2 + P * P) / c,
             1040 * pi * K1 * P / c, 4160 * pi * pi * K1 * K1 / c]
    else:
        v = [26 / c]
        g = [z, z, 520 * pi * K1 / c]
        h = [z, z, 520 * pi * K2 / c, z, 2080 * pi * pi * K1 * K1 / c]
    return tuple(gaussian_poly_sum(c, cf, n0) for cf in (v, g, h))


class LocalChart:
    """X(w)=A(w)(B Z^3 union (B Z^3+B f0+u)); det A=1."""
    def __init__(self, row):
        self.row = row
        scale = arb(2) ** (arb(1) / 3) if row["name"] == "fcc" else arb(1)
        self.B = [[av(x) * scale for x in r] for r in row["period"]]
        self.Bi = [[av(x) / scale for x in r] for r in inv3(row["period"])]
        self.f0 = [av(x) for x in row["offset"]]

    def base(self, wb):
        w = [Jet.var(v, i) for i, v in enumerate(wb)]
        s2, s6 = arb(2).sqrt(), arb(6).sqrt()
        S = [[Jet(0) for _ in range(3)] for _ in range(3)]
        S[0][0] = w[0] * (1 / s2) + w[1] * (1 / s6)
        S[1][1] = w[0] * (-1 / s2) + w[1] * (1 / s6)
        S[2][2] = w[1] * (-2 / s6)
        for k, (i, j) in enumerate(((0, 1), (0, 2), (1, 2)), 2):
            S[i][j] = S[j][i] = w[k] * (1 / s2)
        T = [[S[i][j] + int(i == j) for j in range(3)] for i in range(3)]
        d = det(T)
        if not d.v > 0:
            raise ValueError("strain determinant not certainly positive")
        A = [[d.pow(F(-1, 3)) * x for x in r] for r in T]
        Ai = [[d.pow(F(-2, 3)) * x for x in r] for r in adj(T)]
        BB = mmul(A, self.B)
        BInv = mmul(self.Bi, Ai)
        M = mmul(trans(BB), BB)
        Mi = mmul(BInv, trans(BInv))
        f = [sum((w[j + 5] * self.Bi[i][j] for j in range(3)), Jet(self.f0[i])) for i in range(3)]
        Mf = [sum((M[i][j] * f[j] for j in range(3)), Jet(0)) for i in range(3)]
        fMf = sum((f[i] * Mf[i] for i in range(3)), Jet(0))
        Mc = [list(M[i]) + [Mf[i]] for i in range(3)] + [list(Mf) + [fMf]]
        return {"A": A, "Ai": Ai, "M": M, "Mi": Mi, "Mc": Mc, "f": f, "w": w, "S": S, "d": d}

    def energy_jet(self, wb, n0=6, with_tail=True):
        b = self.base(wb)
        M, Mi, Mc, f = (b[k] for k in ("M", "Mi", "Mc", "f"))
        H = Jet(0)
        for m in itertools.product(range(-n0, n0 + 1), repeat=3):
            H = H + gj(qjet(Mc, m + (1,)), F(1, 2))
            if m > (0, 0, 0):
                phase = linear_combination([(f[i], m[i]) for i in range(3)]) * (2 * arb.pi())
                H = H + gj(qjet(M, m), F(1, 2)) * 2 + gj(qjet(Mi, m), 1) * ((phase.cos() + 1) * 2)
        ac = (8 * arb.pi() / 3) ** (arb(1) / 3)
        e = (H - 4) * (1 / (2 * ac))
        tails = None
        if with_tail:
            trM = sum((M[i][i].v for i in range(3)), arb(0))
            trMi = sum((Mi[i][i].v for i in range(3)), arb(0))
            shift = ubmax(abs(x.v) for x in f)
            Pg = 2 * arb.pi() * arb(3).sqrt() * ubmax(norm_upper(x.g[j] for x in f) for j in range(NV))
            Ph = 2 * arb.pi() * arb(3).sqrt() * ubmax(norm_upper(x.h[j][k] for x in f) for j in range(NV) for k in range(NV))
            tt = [family_tail(M, trMi, n0), family_tail(Mc, trMi, n0, shift=shift),
                  family_tail(Mi, trM, n0, phase_g=Pg, phase_h=Ph, reciprocal=True)]
            tails = [upper(sum((t[j] for t in tt), arb(0)) / (2 * ac)) for j in range(3)]
            e = Jet(e.v + arb(0).union(tails[0]),
                    [x + arb(0, tails[1]) for x in e.g],
                    [[x + arb(0, tails[2]) for x in r] for r in e.h])
        return e, tails, b

    def defect_majorant(self, b):
        if self.row["name"] != "bcc":
            raise ValueError("bcc majorant only")
        A, w = b["A"], b["w"]
        c, Bi = self.row["character"], inv3(self.row["primitive"])
        star = [tuple(F(s, 2) for s in p) for p in itertools.product((-1, 1), repeat=3)]
        star += [tuple(F(s if i == j else 0) for i in range(3)) for j in range(3) for s in (-1, 1)]
        odd = 0
        for e in star:
            m = [sum(Bi[i][j] * e[j] for j in range(3)) for i in range(3)]
            assert all(x.denominator == 1 for x in m)
            odd += int(sum(c[i] * m[i] for i in range(3))) % 2
        Q = sum(((A[i][j] - int(i == j)) * (A[i][j] - int(i == j)) for i in range(3) for j in range(3)), Jet(0)) * 100
        Au = [sum((A[i][j] * w[j + 5] for j in range(3)), Jet(0)) for i in range(3)]
        Q = Q + sum((x * x for x in Au), Jet(0)) * (25 * odd)
        return Q, odd


def ldl_pd(M):
    n = len(M); L = [[arb(0)] * n for _ in range(n)]; d = []
    for j in range(n):
        v = M[j][j] - sum((sq(L[j][k]) * d[k] for k in range(j)), arb(0))
        d.append(v)
        if not v > 0:
            return False, d
        for i in range(j + 1, n):
            L[i][j] = (M[i][j] - sum((L[i][k] * L[j][k] * d[k] for k in range(j)), arb(0))) / v
    return True, d


def eigen_lower(H):
    """Float proposes a bound; exact-ball LDL and row radii certify it."""
    n = len(H)
    HH = [[H[max(i, j)][min(i, j)] for j in range(n)] for i in range(n)]
    if not all(x.is_finite() for r in HH for x in r):
        return None
    M = [[arb(x.mid()) for x in r] for r in HH]
    rad = ubmax(sum((arb(x.rad()) for x in r), arb(0)) for r in HH)
    lam = float(np.linalg.eigvalsh(np.array([[float(x) for x in r] for r in M]))[0])
    for factor in (0.999, 0.99, 0.95, 0.8, 0.5):
        t = arb(lam * factor if lam > 0 else lam / factor)
        ok, _ = ldl_pd([[M[i][j] - (t if i == j else 0) for j in range(n)] for i in range(n)])
        if ok:
            return lower(t - rad)
    return None


def reduced_R(x):
    r1, r2, a, b, c = x[:5]
    r3 = 1 / (r1 * r2)
    return [[r1, r1 * a, r1 * b], [arb(0), r2, r2 * c], [arb(0), arb(0), r3]]


def reduced_positive_lower(x, n0=1):
    """Rigorous lower bound for e from finitely many positive two-site terms.

    Entire eight-dimensional boxes allowed.  It never needs a truncation bound:
    every omitted term is nonnegative.  No interval reciprocal of a possibly
    colliding real-space distance is taken.
    """
    pi = arb.pi(); r1, r2, a, b, c = x[:5]; f = x[5:]
    r3 = 1 / (r1 * r2)
    H = arb(0)
    def real_term(v):
        q = sq(r1 * (v[0] + a * v[1] + b * v[2])) + sq(r2 * (v[1] + c * v[2])) + sq(r3 * v[2])
        qu = upper(q)
        if not qu > 0:
            return arb("+inf")
        return gvalues(pi * qu, F(1, 2), 0)[0]
    for m in itertools.product(range(-n0, n0 + 1), repeat=3):
        H += real_term([m[j] + f[j] for j in range(3)])
        if m > (0, 0, 0):
            H += 2 * real_term(m)
            q = sq(m[0] / r1) + sq((m[1] - a * m[0]) / r2) + sq((m[2] - c * m[1] + (a * c - b) * m[0]) / r3)
            qu = upper(q)
            phase = 2 * pi * sum((m[j] * f[j] for j in range(3)), arb(0))
            fac = max(arb(0), lower(1 + phase.cos()))
            H += 2 * fac * (-pi * qu).exp() / (pi * qu)
    ac = (8 * pi / 3) ** (arb(1) / 3)
    return lower((H - 4) / (2 * ac))


def reduced_invalid(x):
    """Sufficient interval tests that no reduced lattice lies in a box."""
    r1, r2, a, b, c = x[:5]; r3 = 1 / (r1 * r2)
    if sq(r2) < av(F(3, 4)) * sq(r1) or sq(r3) < av(F(3, 4)) * sq(r2):
        return True
    for m in itertools.product((-1, 0, 1), repeat=3):
        if m <= (0, 0, 0):
            continue
        q = sq(r1 * (m[0] + a * m[1] + b * m[2])) + sq(r2 * (m[1] + c * m[2])) + sq(r3 * m[2])
        if q < sq(r1):
            return True
        if m[0] == 0 and (m[1] or m[2]):
            qp = sq(r2 * (m[1] + c * m[2])) + sq(r3 * m[2])
            if qp < sq(r2):
                return True
    return False
