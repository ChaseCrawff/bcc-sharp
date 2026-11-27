"""Local charts of the two-site energy in the isochoric Gram matrix (Section 6).

It uses two_site.py without changing it.  The local
deformation is A=sqrt(C), C=det(I+S)^(-1/3)(I+S), with trace(S)=0.
The implication from these charts to the local inequality is proved in Section 6 of the paper.
"""
from fractions import Fraction as F
import itertools
import math

from flint import arb

from .two_site import (Jet, NV, LocalChart, av, adj, det, mmul, trans,
                       qjet, gj, linear_combination, family_tail, upper, lower,
                       norm_upper, ubmax)
from .two_site import gvalues, gaussian_poly_sum
from .two_site import ldl_pd


def square(x):
    """Nonnegative scalar square enclosure (avoids arb's general power)."""
    hi = upper(abs(x)); hi = upper(hi * hi)
    lo = arb(0) if x.contains(0) else lower(abs(x))
    return lower(lo * lo).union(hi)


def square_jet(x):
    return x.apply(square(x.v), 2 * x.v, arb(2))


def gram_qjet(M, v):
    # v may contain algebraic arb balls, including cancellation balls at zero.
    return linear_combination([(M[i][i], square(v[i])) for i in range(3)] +
                              [(M[i][j], 2 * v[i] * v[j]) for i in range(3) for j in range(i)])


class GramChart(LocalChart):
    """Full eight-dimensional Gram strain + predeformation optical chart."""

    def base(self, wb):
        if len(wb) != 8:
            raise ValueError("eight chart coordinates required")
        w = [Jet.var(v, i) for i, v in enumerate(wb)]
        s2, s6 = arb(2).sqrt(), arb(6).sqrt()
        S = [[Jet(0) for _ in range(3)] for _ in range(3)]
        S[0][0] = w[0] * (1 / s2) + w[1] * (1 / s6)
        S[1][1] = w[0] * (-1 / s2) + w[1] * (1 / s6)
        S[2][2] = w[1] * (-2 / s6)
        for k, (i, j) in enumerate(((0, 1), (0, 2), (1, 2)), 2):
            S[i][j] = S[j][i] = w[k] * (1 / s2)
        T = [[S[i][j] + int(i == j) for j in range(3)] for i in range(3)]
        # trace(S)=0 and ||S||_F^2=sum w_i^2, exactly.  This identity avoids
        # destroying the exact vanishing first derivative of the determinant.
        d = 1 - sum((square_jet(x) for x in w[:5]), Jet(0)) * F(1, 2) + det(S)
        if not d.v > 0:
            raise ValueError("Gram determinant not certainly positive")
        alpha = d.pow(F(-1, 3))
        C = [[alpha * x for x in r] for r in T]
        Ci = [[d.pow(F(-2, 3)) * x for x in r] for r in adj(T)]
        M = mmul(mmul(trans(self.B), C), self.B)
        Mi = mmul(mmul(self.Bi, Ci), trans(self.Bi))
        f = [sum((w[j + 5] * self.Bi[i][j] for j in range(3)), Jet(self.f0[i])) for i in range(3)]
        Mf = [sum((M[i][j] * f[j] for j in range(3)), Jet(0)) for i in range(3)]
        fMf = sum((f[i] * Mf[i] for i in range(3)), Jet(0))
        Mc = [list(M[i]) + [Mf[i]] for i in range(3)] + [list(Mf) + [fMf]]
        Cu = [sum((C[i][j] * w[j + 5] for j in range(3)), Jet(0)) for i in range(3)]
        uCu = sum((w[i + 5] * Cu[i] for i in range(3)), Jet(0))
        return {"C": C, "Ci": Ci, "M": M, "Mi": Mi, "Mc": Mc,
                "f": f, "w": w, "S": S, "d": d, "Cu": Cu, "uCu": uCu}

    def energy_jet(self, wb, n0=7, with_tail=True):
        b = self.base(wb)
        C, Ci, Cu, uCu, f = (b[k] for k in ("C", "Ci", "Cu", "uCu", "f"))
        H = Jet(0)
        for m in itertools.product(range(-n0, n0 + 1), repeat=3):
            a = [sum((self.B[i][j] * (m[j] + self.f0[j]) for j in range(3)), arb(0)) for i in range(3)]
            Q = gram_qjet(C, a) + linear_combination([(Cu[i], 2 * a[i]) for i in range(3)]) + uCu
            H = H + gj(Q, F(1, 2))
            if m > (0, 0, 0):
                a = [sum((self.B[i][j] * m[j] for j in range(3)), arb(0)) for i in range(3)]
                k = [sum((self.Bi[j][i] * m[j] for j in range(3)), arb(0)) for i in range(3)]
                phase = linear_combination([(f[i], m[i]) for i in range(3)]) * (2 * arb.pi())
                H = H + gj(gram_qjet(C, a), F(1, 2)) * 2 + gj(gram_qjet(Ci, k), 1) * ((phase.cos() + 1) * 2)
        ac = (8 * arb.pi() / 3) ** (arb(1) / 3)
        e = (H - 4) * (1 / (2 * ac))
        tails = None
        if with_tail:
            M, Mi, Mc = (b[k] for k in ("M", "Mi", "Mc"))
            trM = sum((M[i][i].v for i in range(3)), arb(0))
            trMi = sum((Mi[i][i].v for i in range(3)), arb(0))
            shift = ubmax(abs(x.v) for x in f)
            Pg = 2 * arb.pi() * arb(3).sqrt() * ubmax(norm_upper(x.g[j] for x in f) for j in range(NV))
            tt = [family_tail(M, trMi, n0), family_tail(Mc, trMi, n0, shift=shift),
                  family_tail(Mi, trM, n0, phase_g=Pg, reciprocal=True)]
            tails = [upper(sum((t[j] for t in tt), arb(0)) / (2 * ac)) for j in range(3)]
            e = Jet(e.v + arb(0).union(tails[0]),
                    [x + arb(0, tails[1]) for x in e.g],
                    [[x + arb(0, tails[2]) for x in r] for r in e.h])
        return e, tails, b


def block(H, start, stop):
    return [r[start:stop] for r in H[start:stop]]


def gram_geometry(radius_s, radius_u):
    """Bounds on product of Euclidean strain/optical balls."""
    s, u = av(radius_s), av(radius_u)
    if not (s >= 0 and u >= 0 and s < 1):
        raise ValueError("invalid product-ball radius")
    # |det S| <= ||S||_F^3/(3 sqrt(6)) for a traceless symmetric 3x3 S.
    delta_coeff = arb(1) / 2 + s / (3 * arb(6).sqrt())
    delta = delta_coeff * s * s
    dmin = lower(1 - delta)
    if not dmin > 0:
        raise ValueError("nonpositive determinant lower bound")
    alpha_max = upper(dmin ** (-arb(1) / 3))
    kappa = (arb(2) / 3).sqrt()
    cmin = lower(1 - kappa * s)
    cmax = upper(alpha_max * (1 + kappa * s))
    amin, amax = lower(cmin.sqrt()), upper(cmax.sqrt())
    # (alpha-1)/||S|| <= (1/3) dmin^(-4/3) delta_coeff * s.
    beta = upper(dmin ** (-arb(4) / 3) * delta_coeff * s / 3)
    cstrain = upper(alpha_max * alpha_max + 3 * beta * beta)
    qstrain = upper(100 * cstrain / square(1 + cmin.sqrt()))
    qoptical = upper(200 * cmax)
    return {"strain_norm_upper": s, "optical_norm_upper": u,
            "determinant_lower": dmin, "gram_spectral_lower": cmin,
            "gram_spectral_upper": cmax, "deformation_singular_lower": amin,
            "deformation_singular_upper": amax,
            "defect_strain_coefficient": qstrain, "defect_optical_coefficient": qoptical,
            "bcc_star_radius_upper": upper(amax * (1 + u)),
            "bcc_other_radius_lower": lower(amin * arb(2).sqrt() - amax * u),
            "fcc_eighteen_radius_upper": upper(amax * (arb(2) ** (arb(1) / 3) + u)),
            "bcc_cross_distance_lower": lower(amin * (arb(3).sqrt() / 2 - u)),
            "fcc_cross_distance_lower": lower(amin * (arb(2) ** (-arb(1) / 6) - u))}


class Series:
    """Univariate order-four Taylor coefficients over arb."""
    __slots__ = ("c",)

    def __init__(self, c):
        self.c = [av(x) for x in c] + [arb(0)] * (5 - len(c))

    def __add__(self, b):
        if not isinstance(b, Series):
            b = Series([b])
        return Series([a + bb for a, bb in zip(self.c, b.c)])
    __radd__ = __add__

    def __neg__(self):
        return self * -1

    def __sub__(self, b):
        return self + (-b)

    def __rsub__(self, b):
        return -self + b

    def __mul__(self, b):
        if not isinstance(b, Series):
            return Series([a * av(b) for a in self.c])
        return Series([sum((self.c[j] * b.c[i - j] for j in range(i + 1)), arb(0)) for i in range(5)])
    __rmul__ = __mul__

    def pow(self, p):
        p = F(p)
        z = Series([0] + self.c[1:])
        out, zz, binom = Series([0]), Series([1]), F(1)
        for k in range(5):
            out = out + zz * (av(binom) * self.c[0] ** av(p - k))
            zz = zz * z
            binom *= (p - k) / (k + 1)
        return out


def gram_radial_bounds(radius):
    """Operator bounds for derivatives of C(t), C(t)^-1 along ||H||F<=1.

    t lies in [-radius,radius], C(t)=det(I+tH)^(-1/3)(I+tH).
    Return order-zero through order-four bounds.  Scalar determinant invariants
    are enclosed independently, which is conservative and uses no samples.
    """
    r = av(radius); kappa = (arb(2) / 3).sqrt()
    delta = 1 / (3 * arb(6).sqrt())
    t = Series([arb(0).union(-r).union(r), 1])
    q = arb(0).union(arb(1))
    d = 1 - t * t * q * F(1, 2) + t * t * t * arb(0, upper(delta))
    if not d.c[0] > 0:
        raise ValueError("radial determinant is not positive")
    alpha, beta = d.pow(F(-1, 3)), d.pow(F(-2, 3))
    aa = [upper(abs(alpha.c[j]) * math.factorial(j)) for j in range(5)]
    bb = [upper(abs(beta.c[j]) * math.factorial(j)) for j in range(5)]
    cc = [upper(aa[j] * (1 + kappa * r) + (j * aa[j - 1] * kappa if j else 0)) for j in range(5)]
    pp = [1 + kappa * r + r * r / 2, kappa + r, arb(1)]
    ci = [upper(sum((math.comb(j, ell) * bb[j - ell] * pp[ell] for ell in range(min(j, 2) + 1)), arb(0))) for j in range(5)]
    # det(I+tH)<=1 by AM-GM, and its lower bound uses the exact trace-free identity.
    dmin = lower(1 - r * r / 2 - delta * r * r * r)
    real_mu = lower(1 - kappa * r)
    recip_mu = lower(dmin ** (arb(1) / 3) / (1 + kappa * r))
    return cc, ci, real_mu, recip_mu


def _padd(a, b):
    out = dict(a)
    for key, v in b.items():
        out[key] = out.get(key, arb(0)) + v
    return out


def _pscale(a, c):
    return {k: v * c for k, v in a.items()}


def _pmul(a, b):
    out = {}
    for i, v in a.items():
        for j, w in b.items():
            key = tuple(x + y for x, y in zip(i, j))
            if sum(key) <= 3:
                out[key] = out.get(key, arb(0)) + v * w
    return out


def _poly_sum(items):
    ans = {}
    for p in items:
        ans = _padd(ans, p)
    return ans


def cubic_structure(optical_scale=F(1)):
    """Homogeneous polynomial data for the eight normalized coordinates."""
    w = [{tuple(int(i == j) for i in range(8)): arb(1)} for j in range(8)]
    u = [_pscale(p, av(optical_scale)) for p in w[5:]]
    s2 = _poly_sum(_pmul(p, p) for p in w[:5])
    U2 = _poly_sum(_pmul(p, p) for p in u)
    S = [[{} for _ in range(3)] for _ in range(3)]
    z2, z6 = 1 / arb(2).sqrt(), 1 / arb(6).sqrt()
    S[0][0] = _padd(_pscale(w[0], z2), _pscale(w[1], z6))
    S[1][1] = _padd(_pscale(w[0], -z2), _pscale(w[1], z6))
    S[2][2] = _pscale(w[1], -2 * z6)
    for k, (i, j) in enumerate(((0, 1), (0, 2), (1, 2)), 2):
        S[i][j] = S[j][i] = _pscale(w[k], z2)
    detS = _poly_sum(_pscale(_pmul(_pmul(S[0][p[0]], S[1][p[1]]), S[2][p[2]]),
                                  (-1) ** sum(p[i] > p[j] for i in range(3) for j in range(i + 1, 3)))
                     for p in itertools.permutations(range(3)))
    uSu = _poly_sum(_pmul(_pmul(u[i], S[i][j]), u[j]) for i in range(3) for j in range(3))
    return S, s2, detS, u, U2, uSu


def _qpolys(a, structure, cross=False, reciprocal=False):
    S, s2, detS, u, U2, uSu = structure
    q0 = sum((square(x) for x in a), arb(0))
    aSa = _poly_sum(_pscale(S[i][j], a[i] * a[j]) for i in range(3) for j in range(3))
    if reciprocal:
        Sa = [_poly_sum(_pscale(S[i][j], a[j]) for j in range(3)) for i in range(3)]
        aS2a = _poly_sum(_pmul(p, p) for p in Sa)
        return q0, _pscale(aSa, -1), _padd(aS2a, _pscale(s2, -q0 / 6)), _padd(_pscale(_pmul(aSa, s2), -arb(1) / 3), _pscale(detS, -2 * q0 / 3))
    q1 = aSa
    q2 = _pscale(s2, q0 / 6)
    q3 = _padd(_pscale(_pmul(aSa, s2), arb(1) / 6), _pscale(detS, -q0 / 3))
    if cross:
        au = _poly_sum(_pscale(u[i], a[i]) for i in range(3))
        aSu = _poly_sum(_pscale(_pmul(S[i][j], u[j]), a[i]) for i in range(3) for j in range(3))
        q1 = _padd(q1, _pscale(au, arb(2)))
        q2 = _padd(q2, _padd(U2, _pscale(aSu, arb(2))))
        q3 = _padd(q3, _padd(uSu, _pscale(_pmul(au, s2), arb(1) / 3)))
    return q0, q1, q2, q3


def _g_cubic(qp, a):
    q0, q1, q2, q3 = qp
    pi = arb.pi(); gs = gvalues(pi * q0, a, 3)
    return _poly_sum((_pscale(q3, -pi * gs[1]), _pscale(_pmul(q1, q2), pi * pi * gs[2]),
                      _pscale(_pmul(_pmul(q1, q1), q1), -pi * pi * pi * gs[3] / 6)))


def central_cubic(chart, n0=7, optical_scale=F(1)):
    """Exact interval-enclosed central cubic polynomial of the finite Ewald sum."""
    structure = cubic_structure(optical_scale); total = {}; pi = arb.pi()
    for m in itertools.product(range(-n0, n0 + 1), repeat=3):
        a = [sum((chart.B[i][j] * (m[j] + chart.f0[j]) for j in range(3)), arb(0)) for i in range(3)]
        total = _padd(total, _g_cubic(_qpolys(a, structure, cross=True), F(1, 2)))
        if m > (0, 0, 0):
            a = [sum((chart.B[i][j] * m[j] for j in range(3)), arb(0)) for i in range(3)]
            total = _padd(total, _pscale(_g_cubic(_qpolys(a, structure), F(1, 2)), arb(2)))
            k = [sum((chart.Bi[j][i] * m[j] for j in range(3)), arb(0)) for i in range(3)]
            qp = _qpolys(k, structure, reciprocal=True)
            parity = sum(2 * chart.row["offset"][j] * m[j] for j in range(3))
            assert parity.denominator == 1
            epsilon = 1 if int(parity) % 2 == 0 else -1
            phase = _poly_sum(_pscale(structure[3][i], 2 * pi * k[i]) for i in range(3))
            extra = _pscale(_pmul(_pmul(phase, phase), qp[1]), epsilon * pi * gvalues(pi * qp[0], 1, 1)[1] / 2)
            total = _padd(total, _pscale(_padd(_pscale(_g_cubic(qp, 1), arb(1 + epsilon)), extra), arb(2)))
    ac = (8 * pi / 3) ** (arb(1) / 3)
    total = _pscale(total, 1 / (2 * ac))
    # Symmetric coefficient tensor norm: a monomial coefficient is the sum of
    # multinomial(3,alpha) equal tensor entries.
    norm2 = arb(0)
    for alpha, coefficient in total.items():
        assert sum(alpha) == 3
        mult = math.factorial(3) // math.prod(math.factorial(x) for x in alpha)
        norm2 += square(coefficient) / mult
    return total, upper(upper(norm2).sqrt())


def _composite_bounds(qder, gs):
    """Absolute derivatives 0..4 of G(a,pi*q(t))."""
    pi = arb.pi(); _, q1, q2, q3, q4 = qder
    return [gs[0], pi * gs[1] * q1,
            pi * pi * gs[2] * q1 * q1 + pi * gs[1] * q2,
            pi ** 3 * gs[3] * q1 ** 3 + 3 * pi * pi * gs[2] * q1 * q2 + pi * gs[1] * q3,
            pi ** 4 * gs[4] * q1 ** 4 + 6 * pi ** 3 * gs[3] * q1 * q1 * q2 +
            pi * pi * gs[2] * (3 * q2 * q2 + 4 * q1 * q3) + pi * gs[1] * q4]


def fourth_derivative_bound(chart, radius, n0=7, optical_scale=F(1)):
    """Uniform fourth radial derivative for ||(strain,u/scale)||_2<=radius.

    The returned finite contribution is supplemented by derivative_tail below.
    Every direction has strain Frobenius norm<=1 and optical norm<=scale.
    """
    r, h = av(radius), av(optical_scale)
    cc, ci, real_mu, recip_mu = gram_radial_bounds(radius)
    pi = arb.pi(); total = arb(0)
    for m in itertools.product(range(-n0, n0 + 1), repeat=3):
        a = [sum((chart.B[i][j] * (m[j] + chart.f0[j]) for j in range(3)), arb(0)) for i in range(3)]
        aa = norm_upper(a); aamin = lower(lower(sum((square(x) for x in a), arb(0))).sqrt())
        amin = lower(aamin - r * h)
        if not amin > 0:
            raise ValueError("radial ball reaches a cross-coset collision")
        qmin = lower(real_mu * amin * amin)
        aa += r * h
        qder = [arb(0)] + [upper(aa * aa * cc[j] + 2 * j * h * aa * cc[j - 1] +
                                     (j * (j - 1) * h * h * cc[j - 2] if j >= 2 else 0)) for j in range(1, 5)]
        total += _composite_bounds(qder, gvalues(pi * qmin, F(1, 2), 4))[4]
        if m > (0, 0, 0):
            a = [sum((chart.B[i][j] * m[j] for j in range(3)), arb(0)) for i in range(3)]
            q0 = sum((square(x) for x in a), arb(0))
            qder = [arb(0)] + [upper(q0 * cc[j]) for j in range(1, 5)]
            total += 2 * _composite_bounds(qder, gvalues(pi * lower(real_mu * q0), F(1, 2), 4))[4]
            k = [sum((chart.Bi[j][i] * m[j] for j in range(3)), arb(0)) for i in range(3)]
            q0 = sum((square(x) for x in k), arb(0))
            qder = [arb(0)] + [upper(q0 * ci[j]) for j in range(1, 5)]
            gb = _composite_bounds(qder, gvalues(pi * lower(recip_mu * q0), 1, 4))
            P = upper(2 * pi * upper(q0).sqrt() * h)
            parity = sum(2 * chart.row["offset"][j] * m[j] for j in range(3))
            assert parity.denominator == 1
            epsilon = 1 if int(parity) % 2 == 0 else -1
            cosbounds = [arb(2) if epsilon == 1 else P * P * r * r / 2,
                         P * P * r, P * P, P ** 4 * r, P ** 4]
            total += 2 * sum((math.comb(4, j) * cosbounds[j] * gb[4 - j] for j in range(5)), arb(0))
    ac = (8 * pi / 3) ** (arb(1) / 3)
    tail = derivative_tail(chart, radius, n0, optical_scale, 4)
    return upper(total / (2 * ac) + tail), tail


def derivative_tail(chart, radius, n0, optical_scale=F(1), order=4):
    """Every omitted radial derivative, of order three or four.

    Shells have at most 26 n^2 points.  For x>=1 and a=1/2 or 1,
    G(a+j,x)<=65 exp(-x)/x for 0<=j<=4.  Polynomial degrees reach eight.
    """
    if order not in (3, 4):
        raise ValueError("only orders three and four supported")
    r, h = av(radius), av(optical_scale)
    cc, ci, real_mu, recip_mu = gram_radial_bounds(radius)
    b = chart.base([arb(0)] * 8)
    trM = upper(sum((b["M"][i][i].v for i in range(3)), arb(0)))
    trMi = upper(sum((b["Mi"][i][i].v for i in range(3)), arb(0)))
    Fshift = ubmax(abs(f) for f in chart.f0)
    pi = arb.pi(); total = arb(0)
    for cross, recip in ((False, False), (True, False), (False, True)):
        invtrace, trace, derivs, mu = (trM, trMi, ci, recip_mu) if recip else (trMi, trM, cc, real_mu)
        nu = lower(1 / invtrace)
        shift = Fshift if cross else arb(0)
        theta = lower(1 - shift / (n0 + 1) - (r * h / (nu.sqrt() * (n0 + 1)) if cross else 0))
        if not theta > 0:
            raise ValueError("tail spectral shift is nonpositive")
        c = lower(pi * mu * nu * theta * theta)
        if not c * (n0 + 1) ** 2 >= 1:
            raise ValueError("derivative tail begins before x>=1")
        # |m+f0|<=sqrt(3)(1+F/(n0+1)) n, and ||B||op<=sqrt(tr B'B).
        U = upper((3 * trace).sqrt() * (1 + shift / (n0 + 1)))
        U += r * h if cross else 0
        K = [arb(0)] + [upper(U * U * derivs[j] + (2 * j * h * U * derivs[j - 1] if cross else 0) +
                                      (j * (j - 1) * h * h * derivs[j - 2] if cross and j >= 2 else 0)) for j in range(1, 5)]
        k1, k2, k3, k4 = K[1:]
        # Polynomials in shell index n, before the shared 65 exp(-cn^2)/(cn^2).
        polys = [[arb(1)], [arb(0), arb(0), pi * k1],
                 [arb(0), arb(0), pi * k2, arb(0), pi * pi * k1 * k1],
                 [arb(0), arb(0), pi * k3, arb(0), 3 * pi * pi * k1 * k2, arb(0), pi ** 3 * k1 ** 3],
                 [arb(0), arb(0), pi * k4, arb(0), pi * pi * (3 * k2 * k2 + 4 * k1 * k3), arb(0),
                  6 * pi ** 3 * k1 * k1 * k2, arb(0), pi ** 4 * k1 ** 4]]
        coeff = [arb(0)] * (2 * order + 1)
        P = upper(2 * pi * h * (3 * trMi).sqrt()) if recip else arb(0)
        for j in range(order + 1 if recip else 1):
            fac = (arb(2) if j == 0 else P ** j) if recip else arb(1)
            fac *= math.comb(order, j)
            for power, val in enumerate(polys[order - j]):
                coeff[power + j] += fac * val
        coeff = [upper(x * 26 * 65 / c) for x in coeff]
        total += gaussian_poly_sum(c, coeff, n0)
    ac = (8 * pi / 3) ** (arb(1) / 3)
    return upper(total / (2 * ac))


def rational_eigen_lower(H, steps=28):
    """Positive eigenvalue lower bound using rational proposals and arb LDL.

    No floating-point eigensolver or floating-point branch participates.
    Each successful LDL test certifies the whole symmetric interval matrix.
    The ceiling two is only a proposal bound; eigenvalues above it cause no loss
    of validity. Failure returns None and never asserts nonpositivity.
    """
    n = len(H)
    HH = [[H[max(i, j)][min(i, j)] for j in range(n)] for i in range(n)]
    if not all(x.is_finite() for row in HH for x in row):
        return None
    if not ldl_pd(HH)[0]:
        return None
    lo, hi = F(0), F(2)
    for _ in range(steps):
        t = (lo + hi) / 2
        test = [[HH[i][j] - (av(t) if i == j else 0) for j in range(n)] for i in range(n)]
        if ldl_pd(test)[0]:
            lo = t
        else:
            hi = t
    return av(lo)


def atlas_check(chart, center_hessian, cubic_norm, cubic_tail, radius,
                optical_scale, gap, n0=8):
    """Sufficient check of the two-site inequality on one whole ellipsoid; all decisions are arb.

    Coordinates z=(w1..w5,u/optical_scale). The domain is ||z||2<=radius.
    """
    r, h = av(radius), av(optical_scale)
    if not (r > 0 and h > 0):
        raise ValueError("positive atlas radius and optical scale required")
    geometry = gram_geometry(radius, radius * optical_scale)
    if chart.row["name"] == "bcc":
        geom_ok = geometry["bcc_star_radius_upper"] < av(F(13, 10)) and geometry["bcc_other_radius_lower"] > av(F(13, 10)) and geometry["bcc_cross_distance_lower"] > 0
    else:
        geom_ok = geometry["fcc_eighteen_radius_upper"] <= av(F(51, 40)) and geometry["fcc_cross_distance_lower"] > 0
    scales = [arb(1)] * 5 + [h] * 3
    H = [[center_hessian[i][j] * scales[i] * scales[j] for j in range(8)] for i in range(8)]
    if chart.row["name"] == "bcc":
        for i in range(8):
            q = geometry["defect_strain_coefficient"] if i < 5 else geometry["defect_optical_coefficient"] * h * h
            H[i][i] -= 2 * gap * q
    lam = rational_eigen_lower(H)
    b4, t4 = fourth_derivative_bound(chart, radius, n0, optical_scale)
    cc, ci, mu_real, mu_recip = gram_radial_bounds(radius)
    b3 = upper(cubic_norm + cubic_tail / 6)
    margin = None if lam is None else lower(lam / 2 - b3 * r - b4 * r * r / 24)
    return {"certified": bool(geom_ok and margin is not None and margin > 0),
            "geometry_certified": bool(geom_ok), "geometry": geometry,
            "quadratic_eigenvalue_lower": lam, "central_cubic_norm_upper": cubic_norm,
            "central_third_derivative_tail_upper": cubic_tail, "total_cubic_coefficient_upper": b3,
            "uniform_gram_derivative_operator_bounds": {"C_orders_0_through_4": cc, "inverse_C_orders_0_through_4": ci,
                                                        "real_spectral_lower": mu_real, "reciprocal_spectral_lower": mu_recip},
            "uniform_fourth_derivative_upper": b4, "fourth_derivative_tail_upper": t4,
            "objective_per_norm_squared_lower": margin}
