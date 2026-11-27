r"""Certified tools for the lattice case (Theorem 5.1): the Coulomb lattice energy in reduced coordinates, with interval jets.

Everything is arb ball arithmetic (python-flint),
so every returned ball contains the exact quantity (Section 9.1 of the paper).

Setting (covolume one; Section 5 of the paper). For a lattice L = R Z^3 of covolume one with upper-triangular basis
    R = [[r1, x r1, y r1], [0, r2, z r2], [0, 0, r3]],   r3 = 1/(r1 r2),   xi = (r1, r2, x, y, z),
the Gram matrix is Y = R^T R, Y[m] = |R m|^2, Y^{-1}[m] = |R^{-T} m|^2, and
    H(xi) := H_{1/2}(Y) = sum_{m != 0} [ G(1/2, pi Y[m]) + G(1, pi Y^{-1}[m]) ],   G(a, x) = int_1^inf e^{-xt} t^{a-1} dt,
with every term positive. The WS-unit energy of Lambda = s L (s = (4 pi/3)^{1/3}) is e(Lambda) = (H(xi) - 3)/(2 s).

A Jet carries a value, a gradient (5) and a Hessian (5x5, symmetric, stored in full) of a function of xi, all as arb balls. When
the variables are balls covering a box, every component encloses the corresponding derivative at every point of the box
(inclusion monotonicity of arb operations); when they are exact points, it encloses the derivatives at that point.
"""

import itertools
import math

from flint import arb

from .two_site import deriv_norms

NV = 5


class Jet:
    __slots__ = ("v", "g", "h")

    def __init__(self, v, g=None, h=None):
        self.v = v
        self.g = g if g is not None else [arb(0)] * NV
        self.h = h if h is not None else [[arb(0)] * NV for _ in range(NV)]

    @staticmethod
    def var(val, i):
        g = [arb(0)] * NV
        g[i] = arb(1)
        return Jet(arb(val), g)

    @staticmethod
    def const(c):
        return Jet(arb(c))

    def __add__(self, o):
        if not isinstance(o, Jet):
            return Jet(self.v + o, self.g, self.h)
        return Jet(self.v + o.v, [a + b for a, b in zip(self.g, o.g)],
                   [[a + b for a, b in zip(ra, rb)] for ra, rb in zip(self.h, o.h)])

    __radd__ = __add__

    def __neg__(self):
        return Jet(-self.v, [-a for a in self.g], [[-a for a in r] for r in self.h])

    def __sub__(self, o):
        return self + (-o if isinstance(o, Jet) else -arb(o))

    def __rsub__(self, o):
        return (-self) + o

    def __mul__(self, o):
        if not isinstance(o, Jet):
            o = arb(o)
            return Jet(self.v * o, [a * o for a in self.g], [[a * o for a in r] for r in self.h])
        v = self.v * o.v
        g = [self.v * b + o.v * a for a, b in zip(self.g, o.g)]
        h = [[self.v * o.h[i][j] + o.v * self.h[i][j] + self.g[i] * o.g[j] + self.g[j] * o.g[i]
              for j in range(NV)] for i in range(NV)]
        return Jet(v, g, h)

    __rmul__ = __mul__

    def apply(self, f0, f1, f2):
        """Compose with a scalar function f, given f(v), f'(v), f''(v) as balls (enclosing them on the value ball)."""
        g = [f1 * a for a in self.g]
        h = [[f2 * self.g[i] * self.g[j] + f1 * self.h[i][j] for j in range(NV)] for i in range(NV)]
        return Jet(f0, g, h)

    def inv(self):
        v = self.v
        return self.apply(1 / v, -1 / (v * v), 2 / (v * v * v))

    def __truediv__(self, o):
        if not isinstance(o, Jet):
            return self * (1 / arb(o))
        return self * o.inv()

    def sq(self):
        return self * self


def G_values(x, a0, order):
    """[G(a0, x), G(a0+1, x), ..., G(a0+order, x)] for a0 in {1/2, 1}, x a ball with x > 0 (G(a+1,x) = (e^{-x} + a G(a,x))/x)."""
    ex = (-x).exp()
    if a0 == 1:
        g = ex / x
        a = arb(1)
    else:
        sx = x.sqrt()
        g = (arb.pi() / x).sqrt() * sx.erfc()
        a = arb(1) / 2
    out = [g]
    for _ in range(order):
        g = (ex + a * g) / x
        a = a + 1
        out.append(g)
    return out


def term_jet(Qj, a0):
    """Jet of G(a0, pi Q) from the jet of Q: d/dQ = -pi G(a0+1, pi Q), d^2/dQ^2 = pi^2 G(a0+2, pi Q)."""
    pi = arb.pi()
    G = G_values(pi * Qj.v, a0, 2)
    return Qj.apply(G[0], -pi * G[1], pi * pi * G[2])


def coords(xi_balls):
    """Jets of r1, r2, x, y, z, r3 from five balls (or points)."""
    r1, r2, x, y, z = [Jet.var(v, i) for i, v in enumerate(xi_balls)]
    r3 = (r1 * r2).inv()
    return r1, r2, x, y, z, r3


def half_set(nmax):
    """One representative of each pair {m, -m} with 0 < |m|_inf <= nmax (lexicographically positive)."""
    out = []
    for m in itertools.product(range(-nmax, nmax + 1), repeat=3):
        if m > (0, 0, 0):
            out.append(m)
    return out


def H_partial(xi_balls, mset):
    """Jet of P(xi) = 2 sum_{m in mset} [G(1/2, pi Y[m]) + G(1, pi Y^{-1}[m])] (mset: one of each +-pair).
    A lower bound for H(xi) (all omitted terms are positive). Y[m] = |R m|^2 and Y^{-1}[m] = |R^{-T} m|^2 are formed per term from
    the jets of R and R^{-T} (this keeps the correlations between the entries of Y; forming m^T Y m from the six entries of Y
    gave wider enclosures)."""
    r1, r2, x, y, z, r3 = coords(xi_balls)
    half = arb(1) / 2
    ir1, ir2, ir3 = r1.inv(), r2.inv(), r3.inv()
    total = Jet.const(0)
    for (m1, m2, m3) in mset:
        u1 = r1 * (x * m2 + y * m3 + m1)
        u2 = r2 * (z * m3 + m2)
        u3 = r3 * m3
        Q = u1.sq() + u2.sq() + u3.sq()
        w1 = ir1 * m1
        w2 = ir2 * (x * (-m1) + m2)
        w3 = ir3 * (y * (-m1) + z * (x * m1 - m2) + m3)
        Qs = w1.sq() + w2.sq() + w3.sq()
        total = total + term_jet(Q, half) + term_jet(Qs, 1)
    return total * 2


def gram_from_xi(xi):
    """Gram matrix Y (3x3 list of balls) at a point/box xi (balls)."""
    r1, r2, x, y, z = xi
    r3 = 1 / (r1 * r2)
    R = [[r1, x * r1, y * r1], [arb(0), r2, z * r2], [arb(0), arb(0), r3]]
    return [[sum((R[k][i] * R[k][j] for k in range(3)), arb(0)) for j in range(3)] for i in range(3)], R


def R_jet(xi_balls):
    r1, r2, x, y, z, r3 = coords(xi_balls)
    Z = Jet.const(0)
    return [[r1, x * r1, y * r1], [Z, r2, z * r2], [Z, Z, r3]]


def Q_defect_jet(xi_balls, Rref_inv, kappa):
    """Jet of Q(xi) = kappa * ||C - I||_F^2 with C = Rref^{-T} R^T R Rref^{-1} = (R Rref^{-1})^T (R Rref^{-1}).
    Rref_inv: 3x3 balls (inverse of the reference basis matrix, upper triangular); kappa: ball."""
    R = R_jet(xi_balls)
    A = [[sum((R[i][k] * Rref_inv[k][j] for k in range(3)), Jet.const(0)) for j in range(3)] for i in range(3)]
    C = [[sum((A[k][i] * A[k][j] for k in range(3)), Jet.const(0)) for j in range(3)] for i in range(3)]
    tot = Jet.const(0)
    for i in range(3):
        for j in range(3):
            d = C[i][j] - (1 if i == j else 0)
            tot = tot + d.sq()
    return tot * kappa, C


def C_matrix(xi, Rref_inv):
    """C (3x3 balls) over a box/point xi (balls), without jets."""
    _, R = gram_from_xi(xi)
    A = [[sum((R[i][k] * Rref_inv[k][j] for k in range(3)), arb(0)) for j in range(3)] for i in range(3)]
    return [[sum((A[k][i] * A[k][j] for k in range(3)), arb(0)) for j in range(3)] for i in range(3)]


def gershgorin(C):
    """Rigorous (lower, upper) bounds for the eigenvalues of a symmetric matrix known to lie in the ball matrix C."""
    lo, hi = None, None
    for i in range(3):
        rad = sum((abs(C[i][j]) for j in range(3) if j != i), arb(0))
        l = C[i][i] - rad
        h = C[i][i] + rad
        lo = l if lo is None else arb(min(lo.lower(), l.lower()))
        hi = h if hi is None else arb(max(hi.upper(), h.upper()))
    return arb(lo.lower()), arb(hi.upper())


def ldl_pd(Hb):
    """Interval LDL^T recursion on a symmetric ball matrix. Returns (True, pivots) if every pivot is > 0, which proves that
    every symmetric matrix in the ball matrix is positive definite; else (False, pivots so far)."""
    n = len(Hb)
    L = [[arb(0)] * n for _ in range(n)]
    d = [arb(0)] * n
    for j in range(n):
        s = Hb[j][j]
        for k in range(j):
            s = s - L[j][k] * L[j][k] * d[k]
        d[j] = s
        if not (s > 0):
            return False, d[:j + 1]
        for i in range(j + 1, n):
            t = Hb[i][j]
            for k in range(j):
                t = t - L[i][k] * L[j][k] * d[k]
            L[i][j] = t / s
    return True, d


def hull(a, b):
    return arb(a).union(arb(b))


def box_balls(lo, hi):
    return [hull(l, h) for l, h in zip(lo, hi)]


NAN = arb("nan")


def _finite(*items):
    """True iff every ball in items (balls, lists of balls, lists of lists, Jets/Jet1s) is finite. The lower-bound functions below
    return NAN otherwise, so that every comparison `bound > threshold` made with their result fails."""
    for it in items:
        if it is None:
            return False
        if isinstance(it, arb):
            if not it.is_finite():
                return False
        elif isinstance(it, (Jet, Jet1)):
            parts = [it.v] + list(it.g) + ([x for row in it.h for x in row] if isinstance(it, Jet) else [])
            if not all(x.is_finite() for x in parts):
                return False
        elif not _finite(*it):
            return False
    return True


def taylor_lower_bound(center, radii, jet_center, hess_box):
    """The bounds of Section 5.2 of the paper (after Muratov and Novaga, Prop. 5): for f C^2 on the box B = prod [c_i - r_i, c_i + r_i]
    with f(c), grad f(c) enclosed by jet_center and the Hessian over B enclosed by hess_box:
        inf_B f >= f(c) - sum_j r_j |d_j f(c)| + 1/2 sum_i min(0, kappa_i) r_i^2,
        kappa_i = H_ii^- - sum_{j != i} |H_ij|^+ r_j / r_i.
    Returns a ball whose lower end is a rigorous lower bound; NAN unless every input is finite."""
    if not _finite(radii, jet_center, hess_box):
        return NAN
    val = jet_center.v
    for j in range(NV):
        val = val - radii[j] * abs(jet_center.g[j])
    for i in range(NV):
        kap = arb(hess_box[i][i].lower())
        for j in range(NV):
            if j != i:
                kap = kap - arb(abs(hess_box[i][j]).upper()) * radii[j] / radii[i]
        if kap.lower() < 0:
            val = val + arb(kap.lower()) * radii[i] * radii[i] / 2
    return arb(val.lower())


# ----------------------------------------------------------------------------------------------- tail bound for Hessians
def Y_and_Yinv_jets(xi_balls):
    """Jets of the 6 entries of Y = R^T R and of Y^{-1} = R^{-1} R^{-T}, as 3x3 lists."""
    r1, r2, x, y, z, r3 = coords(xi_balls)
    Z = Jet.const(0)
    R = [[r1, x * r1, y * r1], [Z, r2, z * r2], [Z, Z, r3]]
    Ri = [[r1.inv(), -(x / r2), (x * z - y) / r3], [Z, r2.inv(), -(z / r3)], [Z, Z, r3.inv()]]
    Y = [[sum((R[k][i] * R[k][j] for k in range(3)), Jet.const(0)) for j in range(3)] for i in range(3)]
    Yi = [[sum((Ri[i][k] * Ri[j][k] for k in range(3)), Jet.const(0)) for j in range(3)] for i in range(3)]
    return Y, Yi


def _family_tail(M, Minv_trace, n0, pi, N_extra=25):
    """Entrywise bound on |d^2/dxi_j dxi_k sum_{|m|_inf > n0} G(a, pi m^T M m)| over the box, for a in {1/2, 1}, where M is a 3x3
    matrix of jets (Y or Y^{-1}) and Minv_trace a ball containing tr(M^{-1}) on the box. See Section 5.2 of the paper.
    lambda_min(M) >= 1/lambda_max(M^{-1}) >= 1/tr(M^{-1}) (M positive definite)."""
    if not Minv_trace.is_finite() or not pi.is_finite():
        return None
    mu = arb((1 / Minv_trace).lower())
    if not (mu.is_finite() and mu > 0):
        return None
    K1, K2 = deriv_norms(M)
    if not (pi * mu * (n0 + 1) ** 2 >= 1):
        return None

    def f(n):
        n = arb(n)
        return 130 / (pi * mu) * (-pi * mu * n * n).exp() * (9 * pi * pi * K1 * K1 * n ** 4 + 3 * pi * K2 * n * n)

    tot = arb(0)
    N = n0 + N_extra
    for n in range(n0 + 1, N + 1):
        tot = tot + f(n)
    rho = (arb(N + 1) / N) ** 4 * (-pi * mu * (2 * N + 1)).exp()
    if not (rho < 1):
        return None
    tot = tot + f(N) * rho / (1 - rho)
    return arb(tot.upper()) if tot.is_finite() else None


def hessian_tail(xi_balls, n0):
    """A ball tau >= 0 with |d^2 (H - P_{n0})/dxi_j dxi_k| <= tau for all j, k, at every point of the box (Lemma B.2)."""
    Y, Yi = Y_and_Yinv_jets(xi_balls)
    pi = arb.pi()
    trY = Y[0][0].v + Y[1][1].v + Y[2][2].v
    trYi = Yi[0][0].v + Yi[1][1].v + Yi[2][2].v
    t1 = _family_tail(Y, trYi, n0, pi)
    t2 = _family_tail(Yi, trY, n0, pi)
    if t1 is None or t2 is None:
        return None
    return t1 + t2


def hessian_matrix(jet):
    return [[jet.h[i][j] for j in range(NV)] for i in range(NV)]


# ----------------------------------------------------------------------------------------------- Weyl-type PD / eigenvalue bound
def lam_min_lower(Hb):
    """Rigorous lower bound (a ball's lower end, returned as arb) for the smallest eigenvalue of every symmetric matrix A with
    A_ij in the ball Hb[max(i,j)][min(i,j)] (the lower triangle; the jets' Hessian balls are not exactly symmetric, and only one
    triangle is used, for the midpoints and the radii alike). Write A = M + E with M the exact, symmetric
    lower-triangle midpoint matrix and |E_ij| <= rad_ij. By Weyl, lambda_min(A) >= lambda_min(M) - ||E||_2
    >= t - max_i sum_j rad_ij (row sums in arb), where t is a float proposal certified by the exact (point) LDL^T of M - t I
    having positive pivots (Sylvester). Returns None if an entry is non-finite or no bound is found."""
    import numpy as np
    n = len(Hb)
    if not all(Hb[i][j].is_finite() for i in range(n) for j in range(i + 1)):
        return None
    L = [[Hb[max(i, j)][min(i, j)] for j in range(n)] for i in range(n)]
    M = [[arb(L[i][j].mid()) for j in range(n)] for i in range(n)]
    rowrad = None
    for i in range(n):
        r = sum((arb(L[i][j].rad()) for j in range(n)), arb(0))
        rowrad = r if rowrad is None or r.upper() > rowrad.upper() else rowrad
    rowrad = arb(rowrad.upper())
    Mf = np.array([[float(M[i][j]) for j in range(n)] for i in range(n)])
    if not np.all(np.isfinite(Mf)):
        return None
    lam = float(np.linalg.eigvalsh(Mf)[0])
    for frac in (0.999, 0.99, 0.95, 0.9, 0.8, 0.5):
        t = arb(lam * frac) if lam > 0 else arb(lam / frac)
        Mt = [[M[i][j] - (t if i == j else 0) for j in range(n)] for i in range(n)]
        ok, _ = ldl_pd(Mt)
        if ok:
            return arb((t - rowrad).lower())
    return None


def taylor_lower_bound2(radii, jet_center, hess_box):
    """max of the bound (5.6) of Section 5.2 (diagonal form, Muratov and Novaga, Prop. 5) and its Weyl variant
        inf_B f >= f(c) - sum_j r_j |d_j f(c)| + 1/2 min(0, lambda_lb) sum_j r_j^2.
    Returns an arb (point) that is a rigorous lower bound, or the diagonal form if the eigenvalue bound is unavailable."""
    a = taylor_lower_bound(None, radii, jet_center, hess_box)
    if not a.is_finite():
        return NAN
    lam = lam_min_lower(hess_box)
    if lam is None:
        return a
    val = jet_center.v
    for j in range(NV):
        val = val - radii[j] * abs(jet_center.g[j])
    if lam < 0:
        val = val + lam * sum((r * r for r in radii), arb(0)) / 2
    b = arb(val.lower())
    return a if a > b else b


# ----------------------------------------------------------------------------------------------- first-order jets (value + gradient)
class Jet1:
    """Value and gradient only (balls); same enclosure semantics as Jet."""
    __slots__ = ("v", "g")

    def __init__(self, v, g=None):
        self.v = v
        self.g = g if g is not None else [arb(0)] * NV

    @staticmethod
    def var(val, i):
        g = [arb(0)] * NV
        g[i] = arb(1)
        return Jet1(arb(val), g)

    def __add__(self, o):
        if not isinstance(o, Jet1):
            return Jet1(self.v + o, self.g)
        return Jet1(self.v + o.v, [a + b for a, b in zip(self.g, o.g)])

    __radd__ = __add__

    def __neg__(self):
        return Jet1(-self.v, [-a for a in self.g])

    def __sub__(self, o):
        return self + (-o if isinstance(o, Jet1) else -arb(o))

    def __mul__(self, o):
        if not isinstance(o, Jet1):
            o = arb(o)
            return Jet1(self.v * o, [a * o for a in self.g])
        return Jet1(self.v * o.v, [self.v * b + o.v * a for a, b in zip(self.g, o.g)])

    __rmul__ = __mul__

    def apply(self, f0, f1):
        return Jet1(f0, [f1 * a for a in self.g])

    def inv(self):
        return self.apply(1 / self.v, -1 / (self.v * self.v))

    def sq(self):
        return Jet1(self.v * self.v, [2 * self.v * a for a in self.g])


def H_partial1(xi_balls, mset):
    """First-order jet of the truncated series P (same terms as H_partial)."""
    r1, r2, x, y, z = [Jet1.var(v, i) for i, v in enumerate(xi_balls)]
    r3 = (r1 * r2).inv()
    ir1, ir2, ir3 = r1.inv(), r2.inv(), r3.inv()
    half = arb(1) / 2
    pi = arb.pi()
    total = Jet1(arb(0))
    for (m1, m2, m3) in mset:
        Q = (r1 * (x * m2 + y * m3 + m1)).sq() + (r2 * (z * m3 + m2)).sq() + (r3 * m3).sq()
        Qs = (ir1 * m1).sq() + (ir2 * (x * (-m1) + m2)).sq() + (ir3 * (y * (-m1) + z * (x * m1 - m2) + m3)).sq()
        for QQ, a0 in ((Q, half), (Qs, 1)):
            G = G_values(pi * QQ.v, a0, 1)
            total = total + QQ.apply(G[0], -pi * G[1])
    return total * 2


def Q_defect_jet1(xi_balls, Rref_inv, kappa):
    r1, r2, x, y, z = [Jet1.var(v, i) for i, v in enumerate(xi_balls)]
    r3 = (r1 * r2).inv()
    Z = Jet1(arb(0))
    R = [[r1, x * r1, y * r1], [Z, r2, z * r2], [Z, Z, r3]]
    A = [[sum((R[i][k] * Rref_inv[k][j] for k in range(3)), Jet1(arb(0))) for j in range(3)] for i in range(3)]
    C = [[sum((A[k][i] * A[k][j] for k in range(3)), Jet1(arb(0))) for j in range(3)] for i in range(3)]
    tot = Jet1(arb(0))
    for i in range(3):
        for j in range(3):
            tot = tot + (C[i][j] - (1 if i == j else 0)).sq()
    return tot * kappa


def mean_value_lower(radii, jet_center, jet_box):
    """Eq. (5.4): inf_B f >= f(c) - sum_j r_j sup_B |d_j f| (mean value theorem). NAN unless every input is finite."""
    if not _finite(radii, jet_center.v, jet_box.g):
        return NAN
    val = jet_center.v
    for r, g in zip(radii, jet_box.g):
        val = val - r * arb(abs(g).upper())
    return arb(val.lower())


def mean_value_upper(radii, jet_center, jet_box):
    """sup_B f <= f(c) + sum_j r_j sup_B |d_j f|. NAN unless every input is finite."""
    if not _finite(radii, jet_center.v, jet_box.g):
        return NAN
    val = jet_center.v
    for r, g in zip(radii, jet_box.g):
        val = val + r * arb(abs(g).upper())
    return arb(val.upper())


def box_quadratic_lower(radii, jet_center, lam):
    """Eq. (5.7): if every Hessian on the box B = c + prod[-r_i, r_i] has lambda_min >= lam > 0, then
        inf_B f >= f(c) + sum_i min_{|v| <= r_i} (g_i v + lam v^2 / 2),
    the separable minimum, -|g_i| r_i + lam r_i^2/2 if |g_i| >= lam r_i, else -g_i^2/(2 lam) (g_i taken at its worst end). The
    boundary branch is used only when |g_i| >= lam r_i is certain; otherwise -g_i^2/(2 lam), the unconstrained minimum, which is
    a lower bound in every case. NAN unless every input is finite."""
    if not (_finite(radii, jet_center.v, jet_center.g, lam) and lam > 0):
        return NAN
    val = jet_center.v
    for r, g in zip(radii, jet_center.g):
        ga = arb(abs(g).upper())
        if ga >= lam * r:
            val = val - ga * r + lam * r * r / 2
        else:
            val = val - ga * ga / (2 * lam)
    return arb(val.lower())
