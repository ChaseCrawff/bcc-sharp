"""The planar expansion (Section 7.4 and Sections C.4, C.5): the fibre bound of Lemma C.8 with the
variants of Remark C.9, the planar energy gain of Lemma C.10 and the energy of an anchor, Lemma C.11.

Notation of the paper:  A_par = [[r1, r1 x], [0, r2]],  a = r1 r2,  c = 1/a,  sigma = (y - x z, z),
and for p in Z^2 \\ {0}
    kappa_p = |A_par^-T p| = sqrt(p1^2/r1^2 + (p2 - x p1)^2/r2^2),   T_p = 2 pi c kappa_p,
    omega_p = pi p.sigma,   W_p = (4 c/kappa_p) exp(-T_p/2),   w_p = W_p cos(omega_p)            (C.9)
"""

from fractions import Fraction
from itertools import product

from flint import arb

from .shape import half_offset
from .balls import ball, gamma_ladder, hull, least, lower, pos_part, sq, upper
from .jets import Jet, best_floor, mean_value_enclosure, variables

P1 = ((1, 0), (0, 1), (1, 1))
P2 = ((1, -1), (1, 2), (2, 1))
P3 = ((2, 0), (0, 2), (2, 2))
P_ALL = P1 + P2 + P3
HALF = Fraction(1, 2)


def positive_modes(n):
    """The p in Z^2 with max|p_i| <= n whose first nonzero coordinate is positive (p > 0 in the paper)."""
    return tuple(p for p in product(range(-n, n + 1), repeat=2) if p > (0, 0))


def sinhc_upper(x):
    """An upper bound for sinh(u)/u for |u| <= x, x an exact nonnegative number (sinhc is increasing)."""
    return arb(1) if x.is_zero() else upper(x.sinh() / x)


def geometric_tail_k2(first, x):
    """sum_{k >= first} k^2 x^k = x^first [first^2/(1-x) + 2 first x/(1-x)^2 + x(1+x)/(1-x)^3]  (after Lemma C.10)."""
    rest = 1 - x
    return x ** first * (first * first / rest + 2 * first * x / (rest * rest) + x * (1 + x) / (rest * rest * rest))


def planar_tail(c_plus, ell_plus, tau_minus, s, j):
    """R_J(s) of Lemma C.7, which increases with c and l_par and decreases with tau:
        R_J(s) = 8 c l_par / (1 - e^(-tau J)) [ 2 e^(-tau J)/(1 - e^(-tau)) + 2 e^(-tau s J)/(1 - e^(-tau s)) ].
    """
    first = 2 * (-tau_minus * j).exp() / (1 - (-tau_minus).exp())
    second = 2 * (-tau_minus * s * j).exp() / (1 - (-tau_minus * s).exp())
    return upper(8 * c_plus * ell_plus / (1 - (-tau_minus * j).exp()) * (first + second))


class Domain:
    """A box in n real variables with its centre, half-widths and the two sets of coordinate jets."""

    def __init__(self, lo, hi):
        self.lo, self.hi = tuple(lo), tuple(hi)
        self.box = tuple(hull(a, b) for a, b in zip(lo, hi))
        self.mid = tuple(ball((a + b) / 2) for a, b in zip(lo, hi))
        self.radii = tuple(upper(ball((b - a) / 2)) for a, b in zip(lo, hi))
        self.jets_mid = variables(self.mid)
        self.jets_box = variables(self.box) if self.lo != self.hi else self.jets_mid

    def enclose(self, function):
        """Enclosure over the box of a function of the coordinate jets: direct value and mean value form."""
        at_mid = function(self.jets_mid)
        over_box = function(self.jets_box)
        return mean_value_enclosure(at_mid.v, over_box, self.radii)

    def floor(self, function):
        """Lower bound over the box: the largest of the interval value and of (5.5), (5.6)."""
        return best_floor(function(self.jets_mid), function(self.jets_box), self.radii)


class ShapeBox(Domain):
    """A shape box S in the coordinates (r1, r2, x, y, z), with the bounds used for the planar tails."""

    def __init__(self, lo, hi):
        super().__init__(lo, hi)
        r1, r2, x = self.box[:3]
        self.c = 1 / (r1 * r2)
        # l_par = max(|A_par e1|, |A_par e2|) (Lemma C.7) and a lower bound for tau = 2 pi c / l_par
        self.ell_plus = upper(r1).max(upper((sq(r1 * x) + sq(r2)).sqrt()))
        self.tau_minus = lower(2 * arb.pi() * lower(self.c) / self.ell_plus)


def mode(xi, p):
    """(c, kappa_p, T_p, omega_p, W_p) as jets in the shape coordinates xi = (r1, r2, x, y, z).

    The positive quantities are formed as exponentials of sums of logarithms, so that their derivatives
    are enclosed in the form W (dc/c - dkappa/kappa - dT/2), which keeps the cancellations inside the sum.
    """
    r1, r2, x, y, z = xi
    log_c = -(r1.log() + r2.log())
    log_kappa = ((r1.inverse() * p[0]).square() + ((x * (-p[0]) + p[1]) * r2.inverse()).square()).log() * (arb(1) / 2)
    t = (log_c + log_kappa + (2 * arb.pi()).log()).exp()
    omega = (y * p[0] + (x * (-p[0]) + p[1]) * z) * arb.pi()          # pi p.sigma, sigma = (y - x z, z)
    w_big = (log_c - log_kappa - t * (arb(1) / 2) + arb(4).log()).exp()
    return log_c.exp(), log_kappa.exp(), t, omega, w_big


def in_plane_sum(xi):
    """a^(-1/2) [ -4 + 4 sum_{n > 0, max|n_i| <= 2} G(1/2, (pi/a) |A_par n|^2) ], a lower bound for the
    in-plane term M(A_par) of (7.8) (proof of Lemma C.8), as a jet in xi = (r1, r2, x, y, z)."""
    r1, r2, x = xi[:3]
    ratio = r1 * r2.inverse()
    inverse_ratio = r2 * r1.inverse()
    total = Jet.constant(-4, len(xi))
    for n in positive_modes(2):
        argument = (ratio * (x * n[1] + n[0]).square() + inverse_ratio * (n[1] * n[1])) * arb.pi()
        g0, g1, g2 = gamma_ladder(HALF, argument.v, 2)
        total = total + argument.apply(g0, -g1, g2) * 4
    return (r1 * r2).inverse().sqrt() * total


def psi(x1, x2, x3, differences):
    """An upper bound for Psi(x1,x2,x3) = (1/4) sum_i x_i (x_j - x_k)^2 / (x_j x_k) from enclosures of the
    positive numbers x_i and of the differences x_j - x_k (keyed by the index of the remaining i)."""
    xs = (x1, x2, x3)
    total = arb(0)
    for i in range(3):
        j, k = (a for a in range(3) if a != i)
        total += upper(xs[i]) * upper(sq(differences[i])) / (4 * lower(xs[j]) * lower(xs[k]))
    return upper(total)


def quadratic_loss(a, b, c, d, e):
    """-min over (x, y) in R^2 of a x^2 + b y^2 - c x - d y - e x y, i.e.
    (b c^2 + a d^2 + e c d) / (4 a b - e^2), for lower bounds a, b > 0 and upper bounds c, d, e >= 0 with
    4 a b > e^2 (end of the proof of Lemma C.8).  Returns None if these conditions fail."""
    a, b, c, d, e = lower(a), lower(b), upper(c), upper(d), upper(e)
    determinant = 4 * a * b - e * e
    if not (a > 0 and b > 0 and determinant > 0):
        return None
    return upper((b * c * c + a * d * d + e * c * d) / determinant)


def fibre_bound(lo, hi, eta):
    """Lemma C.8 with Remark C.9: a lower bound for 2 l_2 e(xi, f), valid for all xi in the shape box
    [lo, hi], all f_par in R^2 and all f_3 with |f_3 - 1/2| <= eta < 1/2.  Returns None if the hypotheses
    (w_p > 0 on S for p in P1 u P3, positivity of the quadratic form) cannot be established.
    """
    if not 0 <= eta < HALF:
        raise ValueError("the band must have half-width below 1/2")
    s = ShapeBox(lo, hi)
    eta_b = ball(eta)
    pi = arb.pi()
    w, wt, t_up, sine, angle, w_big_up, w_jet = {}, {}, {}, {}, {}, {}, {}
    for p in P_ALL:
        w_jet[p] = lambda xi, p=p: mode(xi, p)[4] * mode(xi, p)[3].cos()                  # w_p
        w[p] = s.enclose(w_jet[p])
        wt[p] = s.enclose(lambda xi, p=p: mode(xi, p)[4] * mode(xi, p)[2])               # W_p T_p
        _, _, t_box, omega_box, w_box = mode(s.jets_box, p)
        t_up[p] = upper(t_box.v)
        w_big_up[p] = upper(w_box.v)
        sine[p] = upper(omega_box.v.sin().abs_upper())
        angle[p] = upper(omega_box.v.abs_upper())
    if not all(lower(w[p]) > 0 for p in P1 + P3):
        return None
    growth = {p: sinhc_upper(upper(t_up[p] * eta_b)) for p in P_ALL}
    b_bar = {p: upper(upper(wt[p]) * growth[p] * sine[p]) for p in P_ALL}                # \bar b_p
    # fraktur b = 2 pi c^2 - (1/2) sum_P W_p T_p^2 sinhc^2(T_p eta / 2)
    frak_b = 2 * pi * sq(s.c)
    for p in P_ALL:
        frak_b -= w_big_up[p] * t_up[p] * t_up[p] / 2 * sinhc_upper(upper(t_up[p] * eta_b / 2)) ** 2
    frak_b = lower(frak_b)

    def difference(p, q):                                                                 # |w_p - w_q| on S
        return s.enclose(lambda xi: w_jet[p](xi) - w_jet[q](xi))

    first = [w[p] for p in P1]
    floor1, ceil1 = [lower(v) for v in first], [upper(v) for v in first]
    d01, d02, d12 = difference(P1[0], P1[1]), difference(P1[0], P1[2]), difference(P1[1], P1[2])
    psi_third = psi(*(w[p] for p in P3), (difference(P3[1], P3[2]), difference(P3[0], P3[2]), difference(P3[0], P3[1])))
    plus2 = {p: pos_part(upper(w[p])) for p in P2}                                        # (w_p)_+
    # last sum of fraktur d: [ (|W_i T_i - mean| + W_i T_i (sinhc - 1)) |omega_i| + W_i T_i sinhc |omega_i|^3 / 6 ]
    mean_wt = lambda xi: (mode(xi, P1[0])[4] * mode(xi, P1[0])[2] + mode(xi, P1[1])[4] * mode(xi, P1[1])[2]
                          + mode(xi, P1[2])[4] * mode(xi, P1[2])[2]) * (arb(1) / 3)
    odd_sum = arb(0)
    for p in P1:
        spread = s.enclose(lambda xi, p=p: mode(xi, p)[4] * mode(xi, p)[2] - mean_wt(xi))
        pair = upper(wt[p])
        odd_sum += (spread.abs_upper() + pair * (growth[p] - 1)) * angle[p] + pair * growth[p] * angle[p] ** 3 / 6
    d_prime = sum((b_bar[p] for p in P3), arb(0)) + odd_sum                               # fraktur d'
    e_prime = b_bar[P1[0]] + b_bar[P1[1]] + 2 * sum((b_bar[p] for p in P2), arb(0))       # fraktur e'

    losses = []
    # Lemma C.8: zeta = |A_0 + A_1 e^{i theta_1} + A_2 e^{-i theta_2}|
    frak_a, frak_c, frak_d, frak_e, b1 = arb(1) / 2, arb(0), d_prime, arb(0), arb(0)
    frak_d += b_bar[P1[0]] * d02.abs_upper() / floor1[0] + b_bar[P1[1]] * d12.abs_upper() / floor1[1]
    mu_origin = upper(upper(ceil1[2] / (floor1[0] * floor1[1])).sqrt())                   # mu_(1,-1)
    frak_e += (b_bar[P1[0]] + b_bar[P1[1]]) * mu_origin
    for p, (i, j, k), diff in zip(P2, ((0, 1, 2), (1, 2, 0), (0, 2, 1)), (d01, d12, d02)):
        mu2 = upper(ceil1[k] / (floor1[i] * floor1[j]))                                   # mu_p^2
        lam = upper(mu2 * diff.abs_upper())                                               # lambda_p
        mu = upper(mu2.sqrt())
        frak_a -= 2 * plus2[p] * mu2
        frak_c += 4 * plus2[p] * mu * lam
        b1 += 2 * plus2[p] * lam * lam
        frak_d += 2 * b_bar[p] * lam
        frak_e += 2 * b_bar[p] * mu
    loss = quadratic_loss(frak_a, frak_b, frak_c, frak_d, frak_e)
    if loss is not None:
        losses.append(upper(psi(*first, (d12, d02, d01)) + b1 + loss))
    # Remark C.9, first variant: zeta' = |1 + e^{i theta_1} + e^{-i theta_2}|
    mean_w = lambda xi: (w_jet[P1[0]](xi) + w_jet[P1[1]](xi) + w_jet[P1[2]](xi)) * (arb(1) / 3)
    c_first = sum((s.enclose(lambda xi, p=p: w_jet[p](xi) - mean_w(xi)).abs_upper() for p in P1), arb(0))
    second_sum = sum(plus2.values(), arb(0))
    loss = quadratic_loss(sum(first, arb(0)) / 6 - 2 * second_sum, frak_b, c_first, d_prime, e_prime)
    if loss is not None:
        losses.append(loss)
    # Remark C.9, second variant: a number l with 0 <= l < min_i w_i on S
    reserve = upper(4 * second_sum + least(floor1) / 16)
    if all(f > reserve for f in floor1):
        shifted = [v - reserve for v in first]
        loss = quadratic_loss(reserve / 2 - 2 * second_sum, frak_b, arb(0), d_prime, e_prime)
        if loss is not None:
            losses.append(upper(psi(*shifted, (d12, d02, d01)) + loss))
    if not losses:
        return None

    def baseline(xi):                                                                     # B_0
        c = (xi[0] * xi[1]).inverse()
        total = in_plane_sum(xi) + c.square() * (arb.pi() / 6)
        for p in P_ALL:
            _, _, t, omega, w_big = mode(xi, p)
            total = total + w_big * (t * (arb(-1) / 2)).exp() * (omega * 2).cos()         # (4c/kappa) e^-T cos 2 omega
            total = total + w_big * omega.cos() * (1 if p in P2 else arb(-1) / 2)
        return total

    b0 = s.floor(baseline)
    # B_2: omitted layers of the modes with max|p_i| <= 5 and the modes with max|p_i| >= 6
    r1, r2, x = s.box[:3]
    c_minus, c_plus = lower(s.c), upper(s.c)
    b2 = arb(0)
    for p in positive_modes(5):
        kappa = lower(pos_part(lower(sq(p[0] / r1) + sq((p[1] - p[0] * x) / r2))).sqrt())
        if not kappa > 0:
            return None
        t = lower(2 * pi * c_minus * kappa)
        ratio = (-t).exp()
        e_p = (-t * (ball(HALF) - eta_b)).exp() + (-t * (ball(HALF) + eta_b)).exp()
        nu = 2 * ratio * ratio + ratio * e_p if p in P_ALL else 2 * ratio + e_p
        b2 += 2 * c_plus / kappa * nu / (1 - ratio)
    b2 = upper(b2 + planar_tail(c_plus, s.ell_plus, s.tau_minus, lower(ball(HALF) - eta_b), 6))
    losses = [loss for loss in losses if loss.is_finite()]          # each finite one is a valid bound
    if not losses:
        return None
    return lower(b0 - upper(least(losses) + psi_third) - b2)


# ---------------------------------------------------------------------------------------------
# Lemma 7.7(i): the planar energy rule with Montgomery's theorem
# ---------------------------------------------------------------------------------------------
_TRIANGULAR = {}


def triangular_constant():
    """C <= M_triangle: minus 4 plus the partial sum over max|n_i| <= 3 of the series (7.8) for the triangular
    lattice of area a, for which (pi/a)|A n|^2 and pi a |A^-T n|^2 run over (2 pi/sqrt 3)(i^2 +- i j + j^2)."""
    from flint import ctx
    if ctx.prec not in _TRIANGULAR:
        factor = 2 * arb.pi() / arb(3).sqrt()
        total = arb(-4)
        for i, j in positive_modes(3):
            for form in (i * i + i * j + j * j, i * i - i * j + j * j):
                total += 2 * gamma_ladder(HALF, factor * form, 0)[0]
        _TRIANGULAR[ctx.prec] = lower(total)
    return _TRIANGULAR[ctx.prec]


def layer_bound(box):
    """Lemma 7.7(i) in the version with Montgomery's theorem (details after Lemma C.7): a lower bound for
    2 l_2 e on the box, or None if the box, translated by an integer in f_3 (Lemma 7.2(ii)), does not lie in
    {eta <= f_3 <= 1 - eta} with eta > 0.

    With delta = f_3 - 1/2:  the first two terms of (7.7) are at least C beta + d beta^4, beta = a^(-1/2),
    d = 2 pi (1/12 + inf delta^2), bounded below by a tangent of this convex function; the terms of (C.10)
    with max|p_i| <= 2 (j = 1 in the first sum, j = 0 in the second) are enclosed over the box; the other
    layers of these pairs cost at most (2c/kappa_p)(2 e^(-2T_p) + 2 e^(-(1+eta)T_p))/(1 - e^(-T_p)) and all
    other modes at most R_3(eta).
    """
    lo, hi = box
    shift = lo[7].numerator // lo[7].denominator                     # floor
    f3_lo, f3_hi = lo[7] - shift, hi[7] - shift
    if not (0 < f3_lo and f3_hi < 1):
        return None
    eta = ball(min(f3_lo, 1 - f3_hi))
    distance = max(f3_lo - HALF, HALF - f3_hi, Fraction(0))          # inf |f_3 - 1/2|
    r1, r2, x, y, z = (hull(a, b) for a, b in zip(lo[:5], hi[:5]))
    f1, f2 = hull(lo[5], hi[5]), hull(lo[6], hi[6])
    delta = hull(f3_lo - HALF, f3_hi - HALF)
    pi = arb.pi()
    c = 1 / (r1 * r2)
    c_minus, c_plus = lower(c), upper(c)
    constant = triangular_constant()
    d = lower(2 * pi * (arb(1) / 12 + ball(distance * distance)))
    beta = c.sqrt()                                                  # a^(-1/2)
    stationary = ((-constant / (4 * d)).root(3)).mid()
    anchor = upper(beta).min(lower(beta).max(stationary))
    base = constant * anchor + d * anchor ** 4 + (constant + 4 * d * anchor ** 3) * (beta - anchor)
    layer, axial = arb(0), arb(0)
    for p in positive_modes(2):
        kappa = (sq(p[0] / r1) + sq((p[1] - p[0] * x) / r2)).sqrt()
        if not lower(kappa) > 0:
            return None
        t = 2 * pi * c * kappa
        gamma = pi * (p[0] * y + (p[1] - p[0] * x) * z)              # omega_p
        phi = 2 * pi * (p[0] * f1 + p[1] * f2) + 2 * gamma * delta   # theta_p
        layer += (2 * (-t / 2).exp() * ((t * delta).cosh() * gamma.cos() * phi.cos()
                                         + (t * delta).sinh() * gamma.sin() * phi.sin())
                  + 2 * (-t).exp() * (2 * gamma).cos()) / kappa
        t_low = lower(t)
        axial += (2 * (-2 * t_low).exp() + 2 * (-t_low * (1 + eta)).exp()) / (1 - (-t_low).exp()) / lower(kappa)
    layer = 2 * c * layer
    ell_plus = upper(r1).max(upper((sq(r1 * x) + sq(r2)).sqrt()))
    tau_minus = lower(2 * pi * c_minus / ell_plus)
    tail = upper(2 * c_plus * axial + planar_tail(c_plus, ell_plus, tau_minus, lower(eta), 3))
    return lower(base + layer - tail)


# ---------------------------------------------------------------------------------------------
# Lemma C.10: the planar energy gain about an anchor with f_{0,3} in 1/2 + Z
# ---------------------------------------------------------------------------------------------
class PlanarGain:
    """The interval matrices of Lemma C.10 on a shape box S, for anchors with the given parities
    chi_p = cos(2 pi p.f0_par).  ``matrix(rho1, rho2, eta)`` encloses L / (2 l_2) for all xi in S, where

        e(xi, f) - e(xi, f0) >= (v, t) [L/(2 l_2)] (v, t)^T     for |v_1| <= rho1, |v_2| <= rho2, |t| <= eta,

    with t = delta_3 and v = (delta_1, delta_2) + t sigma.  N = 3 as in the certificate.
    """

    N = 3

    def __init__(self, lo, hi, f0):
        self.f0 = f0 = half_offset(f0)
        if (f0[2] - HALF).denominator != 1:
            raise ValueError("the planar gain needs f_{0,3} in 1/2 + Z")
        self.s = s = ShapeBox(lo, hi)
        pi = arb.pi()
        self.modes = positive_modes(self.N)
        self.chi = {p: (-1) ** (int(2 * (p[0] * f0[0] + p[1] * f0[1])) % 2) for p in self.modes}

        def leading(i, j):               # entry (i, j) of  - sum_p 2 pi^2 chi_p w_p p p^T
            def function(xi):
                total = Jet.constant(0, 5)
                for p in self.modes:
                    if p[i] * p[j]:
                        _, _, _, omega, w_big = mode(xi, p)
                        total = total + w_big * omega.cos() * (-2 * pi * pi * self.chi[p] * p[i] * p[j])
                return total
            return function

        def mixed(i):                    # component i of  l = pi sum_p chi_p W_p T_p sin(omega_p) p
            def function(xi):
                total = Jet.constant(0, 5)
                for p in self.modes:
                    if p[i]:
                        _, _, t, omega, w_big = mode(xi, p)
                        total = total + w_big * t * omega.sin() * (pi * self.chi[p] * p[i])
                return total
            return function

        self.lead = {(i, j): s.enclose(leading(i, j)) for i, j in ((0, 0), (0, 1), (1, 1))}
        self.mix = [s.enclose(mixed(i)) for i in range(2)]
        self.data = {}
        for p in self.modes:
            _, kappa, t, omega, w_big = mode(s.jets_box, p)
            self.data[p] = (kappa.v, t.v, (w_big.v * omega.v.cos()), w_big.v * t.v * omega.v.sin().abs_upper())
        r1, r2, x = s.box[:3]
        # tau^+ = 2 pi c^+ sup (1/r1^2 + (1+|x|)^2/r2^2)^(1/2)
        self.tau_plus = upper(2 * pi * upper(s.c) * upper((sq(1 / r1) + sq((1 + x.abs_upper()) / r2)).sqrt()))
        # the matrix diag(A_par^T A_par, c^2) of (C.14):  |h|^2 = (v, t) diag(...) (v, t)^T
        self.metric = ((sq(r1), sq(r1) * x, arb(0)), (sq(r1) * x, sq(r1 * x) + sq(r2), arb(0)), (arb(0), arb(0), sq(s.c)))
        self.sigma = (s.box[3] - s.box[2] * s.box[4], s.box[4])
        self._cache = {}

    def matrix(self, rho1, rho2, eta):
        key = (rho1, rho2, eta)
        if key in self._cache:
            return self._cache[key]
        if not 0 <= eta < HALF:
            raise ValueError("the planar gain needs |t| <= eta < 1/2")
        s, pi = self.s, arb.pi()
        eta_b = ball(eta)
        rho = (ball(rho1), ball(rho2))
        entries = dict(self.lead)
        errors = [arb(0), arb(0)]
        vertical = 2 * pi * sq(s.c)
        # s of Lemma C.10 and the two tails t_par, t_3
        q = (-(ball(HALF) - eta_b) * s.tau_minus).exp()
        s_tail = upper(16 * upper(s.c) * s.ell_plus * geometric_tail_k2(self.N + 1, q)
                       / (1 - (-s.tau_minus * (self.N + 1)).exp()))
        t_par, t_3 = 8 * pi * pi * s_tail, self.tau_plus * self.tau_plus * s_tail
        for p in self.modes:
            kappa, t, w, mixed_weight = self.data[p]
            t_hi, t_lo = upper(t), lower(t)
            theta_bar = upper(2 * pi * (abs(p[0]) * rho[0] + abs(p[1]) * rho[1]))
            signed = self.chi[p] * w                                                   # chi_p w_p
            loss = upper(pos_part(upper(-signed)) * pi * pi / 6 * theta_bar * theta_bar)
            for (i, j) in entries:
                entries[i, j] = entries[i, j] - loss * p[i] * p[j]
            vertical -= w.abs_upper() * t_hi * t_hi / 2 * sinhc_upper(upper(t_hi * eta_b / 2)) ** 2
            growth = sinhc_upper(upper(t_hi * eta_b))
            mixed_loss = upper(upper(mixed_weight) * pi * (growth * (1 + theta_bar * theta_bar / 6) - 1))
            for i in range(2):
                errors[i] += mixed_loss * abs(p[i])
            varsigma = upper(4 * upper(s.c) / lower(kappa) * (-(ball(Fraction(3, 2)) - eta_b) * t_lo).exp()
                             / (1 - (-t_lo).exp()))
            t_par += varsigma * 4 * pi * pi * (p[0] * p[0] + p[1] * p[1])
            t_3 += varsigma * t_hi * t_hi
        scale = 2 * (8 * pi / 3).root(3)
        off = [self.mix[i] + (-upper(errors[i])).union(upper(errors[i])) for i in range(2)]
        result = (((entries[0, 0] - t_par) / scale, entries[0, 1] / scale, off[0] / scale),
                  (entries[0, 1] / scale, (entries[1, 1] - t_par) / scale, off[1] / scale),
                  (off[0] / scale, off[1] / scale, (vertical - t_3) / scale))
        if len(self._cache) > 64:
            self._cache.clear()
        self._cache[key] = result
        return result


# ---------------------------------------------------------------------------------------------
# Lemma C.11: the energy of an anchor with f_{0,3} in 1/2 + Z, in the variables (r1 r2, r1/r2, x, y, z)
# ---------------------------------------------------------------------------------------------
def anchor_function(u, f0):
    """A_0 of Lemma C.11 as a jet in u = (a, rho, x, y, z), a = r1 r2, rho = r1/r2, where c = 1/a and
    kappa_p^2 = (p1^2/rho + (p2 - p1 x)^2 rho)/a  (text after Lemma C.12)."""
    area, ratio, x, y, z = u
    pi = arb.pi()
    c = area.inverse()
    inverse_ratio = ratio.inverse()
    planar = Jet.constant(-4, 5)
    for n in positive_modes(2):
        argument = (ratio * (x * n[1] + n[0]).square() + inverse_ratio * (n[1] * n[1])) * pi
        g0, g1, g2 = gamma_ladder(HALF, argument.v, 2)
        planar = planar + argument.apply(g0, -g1, g2) * 4
    total = area.inverse().sqrt() * planar + c.square() * (pi / 6)
    for p in positive_modes(3):
        kappa = ((inverse_ratio * (p[0] * p[0]) + ratio * (x * (-p[0]) + p[1]).square()) * c).sqrt()
        omega = (y * p[0] + (x * (-p[0]) + p[1]) * z) * pi
        t = c * kappa * (2 * pi)
        e_half = (t * (arb(-1) / 2)).exp()
        e_one = e_half.square()
        cos2 = (omega * 2).cos()
        chi = (-1) ** (int(2 * (p[0] * f0[0] + p[1] * f0[1])) % 2)
        numerator = e_one * cos2 - e_one.square() + e_half * (1 - e_one) * omega.cos() * chi
        denominator = 1 - e_one * cos2 * 2 + e_one.square()
        total = total + c * kappa.inverse() * 4 * numerator * denominator.inverse()
    return total


def strain_function(u, w):
    """28 |C - I|_F^2 as a jet in u = (a, rho, x, y, z), C = A^T A, A = R B'^-1 (Lemma 7.8(v))."""
    area, ratio, x, y, z = u
    scales = (area * ratio, area * ratio.inverse(), area.inverse().square())          # r1^2, r2^2, r3^2
    rows = (tuple(x * w[1][i] + y * w[2][i] + w[0][i] for i in range(3)),
            tuple(z * w[2][i] + w[1][i] for i in range(3)),
            tuple(Jet.constant(w[2][i], 5) for i in range(3)))
    total = Jet.constant(0, 5)
    for i in range(3):
        for j in range(i + 1):
            entry = scales[0] * rows[0][i] * rows[0][j] + scales[1] * rows[1][i] * rows[1][j] + scales[2] * rows[2][i] * rows[2][j]
            total = total + (entry - int(i == j)).square() * (1 if i == j else 2)
    return total * 28


class AnchorEnergy:
    """Lower bounds over a shape box S for the energy of the anchor (xi, f0), f_{0,3} in 1/2 + Z:

        2 l_2 e(xi, f0) >= A_0(xi) - R_4(1/2)                                       (Lemma C.11)

    ``energy_floor()`` is E_0^- and ``deficit_floor(w)`` is a lower bound for
    inf_S [ (A_0 - R_4(1/2))/(2 l_2) - 28 g^+ |C - I|_F^2 ] with C from the registration matrix W = B'^-1
    (Lemma C.12).  Both are computed in the variables (r1 r2, r1/r2, x, y, z) on the box spanned by
    their ranges.
    """

    def __init__(self, lo, hi, f0):
        self.f0 = f0
        shape_box = ShapeBox(lo, hi)
        r1, r2 = lo[0], lo[1]
        r1p, r2p = hi[0], hi[1]
        u_lo = (r1 * r2, r1 / r2p) + tuple(lo[2:])
        u_hi = (r1p * r2p, r1p / r2) + tuple(hi[2:])
        self.u = Domain(u_lo, u_hi)
        self.scale = 2 * (8 * arb.pi() / 3).root(3)
        self.tail = planar_tail(upper(shape_box.c), shape_box.ell_plus, shape_box.tau_minus, ball(HALF), 4)

    def energy_floor(self):
        return lower((self.u.floor(lambda u: anchor_function(u, self.f0)) - self.tail) / self.scale)

    def deficit_floor(self, w, gap):
        factor = self.scale * gap
        w_ball = tuple(tuple(map(ball, row)) for row in w)
        value = self.u.floor(lambda u: anchor_function(u, self.f0) - strain_function(u, w_ball) * factor)
        return lower((value - self.tail) / self.scale)
