"""The uniform energy-gain form of Lemma C.3 (Section C.1): for a shape box S, a half class f0 and
alpha > 0, a symmetric matrix [H] of intervals with

    e(xi, f) - e(xi, f0) >= delta^T H(xi) delta,     H(xi) in [H],

for all xi in S and f = f0 + n + delta with |delta_i| <= rho_i and |R(xi) delta| <= h_+.

Pairs +-u of Z^3 + f0 contribute through F_r', F_r'' and pairs +-m of Z^3 \\ {0} through F_d, with the
sign eps_m = -cos(2 pi m.f0) (Lemma 7.10(ii), (C.2)).  Parameters as in Remark C.4.
"""

from fractions import Fraction
from itertools import product

from flint import arb

from . import shape
from .balls import Kernels, ball, greatest, hull, lower, pos_part, sq, upper
from .jets import mean_value_enclosure, variables

HALF = Fraction(1, 2)
EXPONENT_LIMIT = 18          # pairs with pi alpha^2 q_u^- > 18 (pi q*_m^-/alpha^2 > 18) go to the tail tau_*
N_R, N_D = 2, 3              # windows max|u_i| <= N_R + 1/2 and max|m_i| <= N_D


def gaussian_tail(c, power, start, terms=24):
    """An upper bound for sum_{k > start} k^power exp(-c k^2): the first ``terms`` terms and Lemma B.3 for
    the rest, with p(n) = n^power, N = start + terms and rho = ((N+1)/N)^power exp(-c (2N+1)) < 1."""
    total = arb(0)
    last = start + terms
    for k in range(start + 1, last + 1):
        total += arb(k) ** power * (-c * k * k).exp()
    ratio = (arb(last + 1) / last) ** power * (-c * (2 * last + 1)).exp()
    if not ratio < 1:
        raise ArithmeticError("Lemma B.3 needs rho < 1")
    return upper(total + arb(last) ** power * (-c * last * last).exp() * ratio / (1 - ratio))


def mat(rows):
    return [list(r) for r in rows]


def matmul(a, b):
    return [[sum((a[i][k] * b[k][j] for k in range(3)), arb(0)) for j in range(3)] for i in range(3)]


def outer(u, v):
    return [[u[i] * v[j] for j in range(3)] for i in range(3)]


def zeros():
    return [[arb(0)] * 3 for _ in range(3)]


def add_scaled(target, factor, source):
    for i in range(3):
        for j in range(3):
            target[i][j] = target[i][j] + factor * source[i][j]


def symmetric(matrix):
    """Symmetrize an interval matrix whose (i, j) and (j, i) entries enclose the same number."""
    out = zeros()
    for i in range(3):
        for j in range(i, 3):
            a, b = matrix[i][j], matrix[j][i]
            low, high = lower(a).max(lower(b)), upper(a).min(upper(b))
            if not low <= high:
                raise ArithmeticError("inconsistent enclosures of a symmetric entry")
            out[i][j] = out[j][i] = low.union(high)
    return out


def six(matrix):
    """Six-number form (11, 22, 33, 12, 13, 23) of a symmetric 3x3 matrix."""
    return (matrix[0][0], matrix[1][1], matrix[2][2], matrix[0][1], matrix[0][2], matrix[1][2])


class GainForm:
    """Lemma C.3 on a shape box [lo, hi] for the half class f0, with the parameters of Remark C.4:
    U, V+- are the pairs with max|u_i| <= 5/2, max|m_i| <= 3 whose exponents at the lower bounds of the
    squared lengths are at most 18; the other pairs of these windows and all pairs outside are charged to
    tau_* by Lemma C.1."""

    def __init__(self, lo, hi, f0, alpha=Fraction(11, 10)):
        self.lo, self.hi = tuple(lo), tuple(hi)
        self.f0 = shape.half_offset(f0)
        kernels = Kernels(alpha)
        pi = arb.pi()
        xi_box = tuple(hull(a, b) for a, b in zip(lo, hi))
        mid = tuple((Fraction(a) + Fraction(b)) / 2 for a, b in zip(lo, hi))
        radii = tuple(upper(ball((Fraction(b) - Fraction(a)) / 2)) for a, b in zip(lo, hi))
        k_exact = shape.gram(mid)                                   # K = M(xi_c), exact
        k_inv_exact = shape.gram_inverse(mid)
        k_full = mat(shape.full(tuple(map(ball, k_exact))))
        kinv_full = mat(shape.full(tuple(map(ball, k_inv_exact))))
        jets_mid = variables(tuple(map(ball, mid)))
        jets_box = variables(xi_box) if self.lo != self.hi else jets_mid

        def enclose(function):
            return mean_value_enclosure(function(jets_mid).v, function(jets_box), radii)

        # enclosures over S of M, of E = M - K and of M^-1 - K^-1, entrywise and by the mean value theorem
        m_six = [enclose(lambda xi, k=k: shape.gram(xi)[k]) for k in range(6)]
        n_six = [enclose(lambda xi, k=k: shape.gram_inverse(xi)[k]) for k in range(6)]
        self.metric = mat(shape.full(tuple(m_six)))                 # [M]
        e_full = mat(shape.full(tuple(m - ball(k) for m, k in zip(m_six, k_exact))))
        # W >= |R^-T e_i|^2 = (M^-1)_ii and Z >= |R e_i|^2 = M_ii on S  (Lemma C.1)
        w_bound = greatest(upper(n_six[i]) for i in range(3))
        z_bound = greatest(upper(m_six[i]) for i in range(3))
        c_r, c_d = lower(kernels.rate_r / w_bound), lower(kernels.rate_d / z_bound)
        if not c_r * (N_R + 1) ** 2 >= 1:
            raise ArithmeticError("Lemma C.1(ii) needs c_r (N_r + 1)^2 >= 1")
        tail = 84 * kernels.alpha * w_bound * gaussian_tail(c_r, 0, N_R) + 52 * pi * gaussian_tail(c_d, 2, N_D)

        u0, u2 = zeros(), zeros()            # U_0 = 4 sum F_r''(qbar) u u^T,  U_2 = -4 sum F_r'''(qbar) u u^T
        a0 = arb(0)                          # sum [phi_u + s_u (qbar_u - q_u^-)]
        a1 = zeros()                         # sum s_u u u^T, so that a_1[X] = <a1, X>
        v0 = zeros()                         # V_0
        self.triples = []                    # (4 F_r'''(qbar_u), u) for U_1[X] = sum 4 F_r''' (u^T X u) u u^T
        self.dual_lin = []                   # (coefficient, m): V_1[X] = sum coefficient (m^T X m) m m^T
        self.dual_quartic = []               # (F_d(q*_m^-), m) for m in V+ :  V_2
        # --- pairs +-u of Z^3 + f0 with max|u_i| <= N_R + 1/2 ---
        doubled = [range(-(2 * N_R + int(2 * f % 2 != 0)), 2 * N_R + 2, 2) if (2 * f) % 2 else range(-2 * N_R, 2 * N_R + 1, 2)
                   for f in self.f0]
        for twice in product(*doubled):
            if not twice > (0, 0, 0):
                continue
            u_exact = tuple(Fraction(v, 2) for v in twice)
            u = tuple(map(ball, u_exact))
            q = sq_norm(shape.real_vector(xi_box, u))
            q_minus, q_plus = lower(q), upper(q)
            if not q_minus > 0:
                raise ArithmeticError("a vector of the anchor could vanish on the shape box")
            if kernels.rate_r * q_minus > EXPONENT_LIMIT:
                tail += lambda_r(kernels, q_minus)
                continue
            q_bar = ball(shape.quad(k_exact, u_exact))
            first_minus = 2 * kernels.f_r(q_minus, 1)[1]            # psi = 2 F_r' at q^-
            derivatives = kernels.f_r(q_plus, 2)
            slope = secant(q_minus, q_plus, first_minus, 2 * derivatives[1], 2 * derivatives[2])
            a0 += first_minus + slope * (q_bar - q_minus)
            uu = outer(u, u)
            add_scaled(a1, slope, uu)
            at_bar = kernels.f_r(q_bar, 3)
            add_scaled(u0, 4 * at_bar[2], uu)
            add_scaled(u2, -4 * at_bar[3], uu)
            self.triples.append((4 * at_bar[3], u))
        # --- pairs +-m of Z^3 \ {0} with max|m_i| <= N_D ---
        for m in product(range(-N_D, N_D + 1), repeat=3):
            if not m > (0, 0, 0):
                continue
            q = sq_norm(shape.dual_vector(xi_box, tuple(arb(v) for v in m)))
            q_minus, q_plus = lower(q), upper(q)
            if not q_minus > 0:
                raise ArithmeticError("a reciprocal vector could vanish on the shape box")
            odd = int(2 * sum(a * b for a, b in zip(m, self.f0))) % 2        # eps_m = +1 iff 2 m.f0 is odd
            if kernels.rate_d * q_minus > EXPONENT_LIMIT:
                if not odd:
                    tail += upper(4 * pi * (-kernels.rate_d * q_minus).exp())
                continue
            q_bar = ball(shape.quad(k_inv_exact, m))
            mm = outer(m, m)
            if odd:                                                  # eps_m = +1: tangent of 4 pi^2 F_d at qbar*
                value, derivative = kernels.f_d(q_bar, 1)
                add_scaled(v0, 4 * pi * pi * value, mm)
                self.dual_lin.append((4 * pi * pi * derivative, m))
                self.dual_quartic.append((kernels.f_d(q_minus)[0], m))
            else:                                                    # eps_m = -1: psi = -4 pi^2 F_d on [q*-, q*+]
                at_minus = -4 * pi * pi * kernels.f_d(q_minus)[0]
                value_plus, derivative_plus = kernels.f_d(q_plus, 1)
                slope = secant(q_minus, q_plus, at_minus, -4 * pi * pi * value_plus, -4 * pi * pi * derivative_plus)
                add_scaled(v0, at_minus + slope * (q_bar - q_minus), mm)
                self.dual_lin.append((slope, m))
        a0 -= upper(tail)
        self.tail = upper(tail)

        # terms of order zero:  K U_0 K + a_0 K + V_0
        ku0 = matmul(k_full, u0)
        base = matmul(ku0, k_full)
        add_scaled(base, a0, k_full)
        add_scaled(base, 1, v0)
        # terms of first order, entry (i, j):  L_ij : E + L*_ij : (M^-1 - K^-1), enclosed through the rational
        # function  L : M + L* : M^-1  of the five shape coordinates
        ku = [(coefficient, u, [sum((k_full[i][k] * u[k] for k in range(3)), arb(0)) for i in range(3)])
              for coefficient, u in self.triples]
        linear = zeros()
        for i in range(3):
            for j in range(i, 3):
                primal = zeros()
                for a in range(3):                                   # (E U_0 K + K U_0 E)_ij
                    primal[i][a] += ku0[j][a]
                    primal[j][a] += ku0[i][a]
                for coefficient, u, image in ku:                     # (K U_1[E] K)_ij
                    add_scaled(primal, coefficient * image[i] * image[j], outer(u, u))
                primal[i][j] += a0                                   # (a_0 E)_ij
                add_scaled(primal, k_full[i][j], a1)                 # (a_1[E] K)_ij
                dual = zeros()
                for coefficient, m in self.dual_lin:                 # V_1[M^-1 - K^-1]_ij
                    if m[i] * m[j]:
                        add_scaled(dual, coefficient * (m[i] * m[j]), outer(m, m))
                l6, d6 = sym_six(primal), sym_six(dual)
                offset = shape.contract(l6, tuple(map(ball, k_exact))) + shape.contract(d6, tuple(map(ball, k_inv_exact)))
                value = enclose(lambda xi: jet_contract(l6, shape.gram(xi)) + jet_contract(d6, shape.gram_inverse(xi)))
                linear[i][j] = linear[j][i] = value - offset
        # terms of higher order in E:  E U_1[E] K + K U_1[E] E + E U_1[E] E + a_1[E] E
        u1 = zeros()
        for coefficient, u in self.triples:
            add_scaled(u1, coefficient * quad_full(e_full, u), outer(u, u))
        eu1 = matmul(e_full, u1)
        higher = matmul(eu1, k_full)
        add_scaled(higher, 1, [list(r) for r in zip(*higher)])       # + transpose: K U_1[E] E
        add_scaled(higher, 1, matmul(eu1, e_full))
        add_scaled(higher, sum((a1[i][j] * e_full[i][j] for i in range(3) for j in range(3)), arb(0)), e_full)
        self.base = [[base[i][j] + linear[i][j] for j in range(3)] for i in range(3)]
        add_scaled(self.base, 1, symmetric(higher))
        self.real_loss = symmetric(matmul(matmul(self.metric, u2), self.metric))          # M U_2 M
        self.scale = 2 * (8 * pi / 3).root(3)
        self.xi_box = xi_box

    def matrix(self, rho, h2_upper):
        """[H] for |delta_i| <= rho_i (exact rationals) and |R(xi) delta|^2 <= h2_upper on S."""
        pi = arb.pi()
        result = [[self.base[i][j] - h2_upper * self.real_loss[i][j] for j in range(3)] for i in range(3)]
        for value, m in self.dual_quartic:                           # V_2 = (pi^2/3) sum F_d(q*-) thetabar^2 m m^T
            theta_bar = 2 * pi * sum((abs(k) * ball(r) for k, r in zip(m, rho)), arb(0))
            add_scaled(result, -(pi * pi / 3) * value * theta_bar * theta_bar, outer(m, m))
        return tuple(tuple(v / self.scale for v in row) for row in result)


def sq_norm(v):
    return sum((sq(x) for x in v), arb(0))


def lambda_r(kernels, q):
    """lambda_r(q) = 2 alpha exp(-pi alpha^2 q) (1 + 1/(2 pi alpha^2 q)) / q >= 2 |F_r'(q)|   (Lemma C.1)."""
    x = kernels.rate_r * q
    return upper(2 * kernels.alpha * (-x).exp() * (1 + 1 / (2 * x)) / q)


def secant(q_minus, q_plus, value_minus, value_plus, derivative_plus):
    """The slope s of (C.4) for an increasing concave psi on [q^-, q^+]: the chord if q^+ - q^- > 1e-9, and
    otherwise a nonnegative lower bound for psi'(q^+)."""
    if q_plus - q_minus > ball(Fraction(1, 10 ** 9)):
        return (value_plus - value_minus) / (q_plus - q_minus)
    return pos_part(lower(derivative_plus))


def sym_six(matrix):
    """Six-number form of the symmetric part of a 3x3 coefficient matrix L (for the pairing L : X with
    symmetric X)."""
    return (matrix[0][0], matrix[1][1], matrix[2][2], (matrix[0][1] + matrix[1][0]) / 2,
            (matrix[0][2] + matrix[2][0]) / 2, (matrix[1][2] + matrix[2][1]) / 2)


def jet_contract(coefficients, six_jets):
    """sum_ab L_ab X_ab for L in six-number form (balls) and X in six-number form (jets)."""
    return (six_jets[0] * coefficients[0] + six_jets[1] * coefficients[1] + six_jets[2] * coefficients[2]
            + (six_jets[3] * coefficients[3] + six_jets[4] * coefficients[4] + six_jets[5] * coefficients[5]) * 2)


def quad_full(matrix, u):
    return sum((matrix[i][j] * u[i] * u[j] for i in range(3) for j in range(3)), arb(0))
