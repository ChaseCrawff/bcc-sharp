"""Lower bounds for the energy on a box: the supports of Lemma 7.5.

By (7.2), for every alpha > 0,

    2 l_2 e(kappa) = sum_{m != 0} F_r(q_m) + sum_m F_r(q^x_m) + sum_{m != 0} w(m.f) F_d(q*_m) - 2 alpha - 2/alpha^2,

with w(t) = 1 + cos(2 pi t) and nonnegative terms.  A *support* bounds finitely many of these terms from
below by a function that is separately concave in the eight coordinates, so that its minimum over a box
is attained at one of the 256 vertices (Lemma 7.4 and the vertex principle).  Three kinds are used:

  TangentSupport      Lemma 7.5(ii), forms (a), (b), (c); base points = an average over the vertices
  ExponentialSupport  Lemma 7.5(iii); base points at the centre of the box
  VertexMaxSupport    Lemma 7.5(ii)(a) or (iii) with constant phase bounds and base points at the vertex
                      maxima, optionally with the phase reserve of Lemma 7.5(iii')

All of them reduce to a function of the form

    S(kappa) = c0 + <A, M> + <A*, M^-1> + 2 b.(M f) + c f^T M f + e.f - sum_k l_k / F_d(q*_{m_k})        (*)

(M = R^T R; A, A* symmetric matrices; b, e vectors), which is evaluated at the vertices by ``Form``.
"""

from fractions import Fraction
from itertools import product
from math import ceil, floor, lcm

from flint import arb, arb_mat

from . import shape
from .balls import Kernels, ball, ell2, greatest, hull, least, lower, sq, upper
from .boxes import centre, contains, offset_vertices, shape_vertices

GRID = 4096  # denominators of the recorded mixtures
DOUBLE = (1, 1, 1, 2, 2, 2)  # <A, M> = sum_k DOUBLE[k] A[k] M[k] in the six-number form


def lex_positive(m):
    """m > 0 in the lexicographic order: one representative of each pair +-m."""
    return m > (0, 0, 0)


def minimum(values):
    """The least lower endpoint of a list of balls (an exact number); rejects non-finite balls."""
    if not values or not all(v.is_finite() for v in values):
        raise ArithmeticError("non-finite vertex value")
    return least(lower(v) for v in values)


def term_window(cube):
    return product(range(-cube, cube + 1), repeat=3)


class Form:
    """The coefficients of a function (*) and its evaluation at the 256 vertices of a box."""

    def __init__(self):
        self.constant = arb(0)
        self.a_m = [arb(0)] * 6       # A
        self.a_n = [arb(0)] * 6       # A*
        self.b = [arb(0)] * 3
        self.c = arb(0)
        self.e = [arb(0)] * 3
        self.losses = []              # (m, l): the term  - l / F_d(q*_m)

    def add_direct(self, coefficient, m, cross):
        """Add coefficient * |R m|^2 (same-coset) or coefficient * |R (m + f)|^2 (cross-coset)."""
        self.a_m = [t + coefficient * k for t, k in zip(self.a_m, shape.moments(m))]
        if cross:
            self.b = [t + coefficient * k for t, k in zip(self.b, m)]
            self.c += coefficient

    def add_dual(self, coefficient, m):
        """Add coefficient * |R^-T m|^2."""
        self.a_n = [t + coefficient * k for t, k in zip(self.a_n, shape.moments(m))]

    def add_phase(self, coefficient, m):
        """Add coefficient * (m.f)."""
        self.e = [t + coefficient * k for t, k in zip(self.e, m)]

    def vertices(self, box, kernels=None, shape_shift=None):
        """Balls S(v) at the 256 vertices of ``box`` (vertex number 8 * shape vertex + offset vertex).
        ``shape_shift(xi)``, if given, is subtracted at every shape vertex (Lemma 7.5(iv))."""
        shapes = [tuple(map(ball, s)) for s in shape_vertices(box)]
        offsets = [tuple(map(ball, f)) for f in offset_vertices(box)]
        grams = [shape.gram(xi) for xi in shapes]
        inverses = [shape.gram_inverse(xi) for xi in shapes]
        base = []
        for xi, gram, inverse in zip(shapes, grams, inverses):
            value = self.constant + shape.contract(self.a_m, gram) + shape.contract(self.a_n, inverse)
            for m, loss in self.losses:
                value -= loss * kernels.inv_f_d(shape.quad(inverse, m))
            if shape_shift is not None:
                value -= shape_shift(xi)
            base.append(value)
        # 2 b.(M f) + c f^T M f = <P_f, M> with P_f = c f f^T + b f^T + f b^T
        pairs = shape.PAIRS
        columns = [[self.c * f[i] * f[j] + self.b[i] * f[j] + self.b[j] * f[i] if i != j
                    else self.c * f[i] * f[i] + 2 * self.b[i] * f[i] for i, j in pairs] for f in offsets]
        gram_matrix = arb_mat([[g[k] * DOUBLE[k] for k in range(6)] for g in grams])            # 32 x 6
        offset_matrix = arb_mat([[columns[o][k] for o in range(8)] for k in range(6)])          # 6 x 8
        mixed = (gram_matrix * offset_matrix).entries()                                        # 32 x 8, row-major
        linear = [shape.dot(self.e, f) for f in offsets]
        return [base[s] + mixed[8 * s + o] + linear[o] for s in range(32) for o in range(8)]


class Centre:
    """Exact squared lengths at the centre of a box and exact phase ranges over its offset box, in integer
    arithmetic over a common denominator.  ``same(m)``, ``cross(m)``, ``dual(m)`` return the squared length
    |R m|^2, |R (m + f)|^2, |R^-T m|^2 at the centre if it is positive and at most ``limit``, else None."""

    def __init__(self, dom, limit):
        mid = centre(dom)
        gram, inverse = shape.gram(mid[:5]), shape.gram_inverse(mid[:5])
        image = shape.sym_apply(gram, mid[5:])                     # M f at the centre
        constant = shape.dot(image, mid[5:])                       # f^T M f at the centre
        numbers = list(gram) + list(inverse) + list(image) + [constant, Fraction(limit)]
        self.den = den = lcm(*(x.denominator for x in numbers))
        scaled = [int(x * den) for x in numbers]
        self.gram, self.inverse, self.image = scaled[:6], scaled[6:12], scaled[12:15]
        self.constant, self.limit = scaled[15], scaled[16]
        offsets = list(dom[0][5:]) + list(dom[1][5:])
        self.offset_den = lcm(*(x.denominator for x in offsets))
        self.lo = [int(x * self.offset_den) for x in dom[0][5:]]
        self.hi = [int(x * self.offset_den) for x in dom[1][5:]]

    def _value(self, numerator):
        return Fraction(numerator, self.den) if 0 < numerator <= self.limit else None

    def same(self, m):
        return self._value(shape.quad(self.gram, m))

    def cross(self, m):
        return self._value(shape.quad(self.gram, m) + 2 * shape.dot(self.image, m) + self.constant)

    def dual(self, m):
        return self._value(shape.quad(self.inverse, m))

    def phase_range(self, m):
        """Exact range [t_L, t_R] of m.f over the offset box."""
        low = sum(min(k * a, k * b) for k, a, b in zip(m, self.lo, self.hi))
        high = sum(max(k * a, k * b) for k, a, b in zip(m, self.lo, self.hi))
        return Fraction(low, self.offset_den), Fraction(high, self.offset_den)


def phase_range(m, lo_f, hi_f):
    """Exact range [t_L, t_R] of m.f over the offset box."""
    return (sum(min(k * a, k * b) for k, a, b in zip(m, lo_f, hi_f)),
            sum(max(k * a, k * b) for k, a, b in zip(m, lo_f, hi_f)))


def meets_half_integers(t_left, t_right):
    return ceil(t_left - Fraction(1, 2)) <= floor(t_right - Fraction(1, 2))


def secant(t_left, t_right):
    """(p, b) of (7.4) for the phase interval [t_left, t_right], or None if it meets Z + 1/2."""
    if meets_half_integers(t_left, t_right):
        return None
    w_left, w_right = (2 * c * c for c in (ball(t_left).cos_pi(), ball(t_right).cos_pi()))   # w = 2 cos^2(pi t)
    if not (w_left > 0 and w_right > 0):
        return None
    if t_left == t_right:
        return w_left, arb(0)
    return (w_left * w_right).sqrt(), (w_right.log() - w_left.log()) / ball(t_right - t_left)


def phase_floor(t_left, t_right):
    """omega with 0 <= omega <= w(t) on [t_left, t_right]: 0 if the interval meets Z + 1/2, and otherwise the
    smaller of the values of w at the two ends (w has no interior minimum between two points of Z + 1/2)."""
    if meets_half_integers(t_left, t_right):
        return arb(0)
    values = [lower(2 * c * c) for c in (ball(t_left).cos_pi(), ball(t_right).cos_pi())]
    return values[0].min(values[1]).max(arb(0))


def vertex_distribution(mix):
    """The probability distribution on the 256 vertices described by a recorded mixture.

    Start from the uniform distribution; each step [v, n] replaces p by (1 - n/4096) p + (n/4096) delta_v.
    Returns (weight of the uniform part, {vertex: extra weight}); exact rationals summing to one.
    """
    uniform, extra = Fraction(1), {}
    for v, n in mix:
        if type(v) is not int or type(n) is not int or not 0 <= v < 256 or not 0 < n <= GRID:
            raise ValueError("invalid mixture step")
        t = Fraction(n, GRID)
        uniform *= 1 - t
        extra = {k: w * (1 - t) for k, w in extra.items()}
        extra[v] = extra.get(v, Fraction(0)) + t
    assert uniform + sum(extra.values()) == 1
    return uniform, extra


class Support:
    """Common part: the box ``dom`` on which the support is built and inside which it may be used."""

    def _set_dom(self, dom):
        """The squared lengths are separately convex on (0, inf)^2 x R^6 (Lemma 7.4); bounds that are taken from
        the vertices of ``dom`` (the capacities of the phase reserve) need ``dom`` inside this set."""
        if not (len(dom[0]) == 8 and len(dom[1]) == 8 and all(a <= b for a, b in zip(*dom)) and dom[0][0] > 0 and dom[0][1] > 0):
            raise ValueError("the box of a support needs eight ordered intervals with r1 > 0 and r2 > 0")
        self.dom = dom

    def _check(self, box):
        if not contains(self.dom, box):
            raise ValueError("a support is valid only inside the box on which it was built")

    def reduced_shift(self, variant, rho, box):
        """Lemma 7.5(iv): the function lambda * c with c = c_1 = r2^2 - (3/4) r1^2 (variant 1) or
        c = c_2 = r2^2 + r1^2 x^2 - r1^2 (variant 2) and lambda = rho * (a lower bound of lambda_{e_1}),
        0 <= rho <= 1.  On reduced shapes c >= 0, so subtracting it keeps a lower bound there, and the
        coefficient of r1^2 stays nonnegative, so the support stays separately concave."""
        rho = Fraction(rho)
        if variant not in (1, 2) or not 0 <= rho <= 1:
            raise ValueError("invalid reduced variant")
        if variant == 1 and not (-Fraction(1, 2) <= box[0][2] and box[1][2] <= Fraction(1, 2)):
            raise ValueError("c_1 >= c_2 needs x^2 <= 1/4 on the box (proof of Lemma 7.5(iv))")
        if self.lambda_e1 is None:
            raise ValueError("the support does not contain the pair of e_1")
        lam = lower(ball(rho) * lower(self.lambda_e1)).max(arb(0))
        if variant == 1:
            return lambda xi: lam * (xi[1] * xi[1] - ball(Fraction(3, 4)) * xi[0] * xi[0])
        return lambda xi: lam * (xi[1] * xi[1] + xi[0] * xi[0] * (xi[2] * xi[2] - 1))


class TangentSupport(Support):
    """A tangent support on the box ``dom`` (Lemma 7.5(ii)), valid on every box contained in ``dom``.

    Terms J: all terms of (7.2) with max|m_i| <= cube whose squared length at the centre of ``dom`` is
    positive and at most ``limit``.  The omitted terms are nonnegative.

    Base points: Q_j, T_j are the averages of q_j, t_j over the vertices of ``dom`` with respect to the
    distribution given by ``mix``.  They are free parameters of Lemma 7.5(ii); only the strength of the
    bound depends on them.

    Direct terms use (ii)(a):  tau = F(Q) + F'(Q) (q - Q), by (7.3).
    A reciprocal pair +-m with phase t = m.f in [t_L, t_R] on ``dom`` uses
      (ii)(b) if [t_L, t_R] contains no point of Z + 1/2:  the tangent plane at (Q, T) of
              2 F_d(q) p exp(b (t - t_0)),  p, b, t_0 from the chord of log w, (7.4);
      (ii)(c) if |t - k - 1/2| <= d <= 1/2 on ``dom``:  2 u zeta - u^2 / (c_d 2 F_d(q)),  zeta = t - k - 1/2,
              c_d = 2 (sin(pi d)/d)^2, (7.5), with u := zeta(T) / (average of 1/(c_d 2 F_d(q)) over the vertices).
    Form (c) is considered when no chord exists or d <= 1/5; when both forms exist, the one with the
    larger value at the base point is taken.  Any of these choices is admissible in Lemma 7.5(ii).
    """

    lambda_e1 = None

    def __init__(self, dom, alpha, cube, limit, mix):
        self._set_dom(dom)
        self.kernels = kernels = Kernels(alpha)
        uniform, extra = vertex_distribution(mix)
        shapes = shape_vertices(dom)
        offsets = offset_vertices(dom)
        grams = [shape.gram(tuple(map(ball, s))) for s in shapes]
        inverses = [shape.gram_inverse(tuple(map(ball, s))) for s in shapes]
        offs = [tuple(map(ball, f)) for f in offsets]

        # Averages over the vertices for the distribution p = uniform part + point masses.  For the uniform
        # part shape and offset are independent, so E[M f] = E[M] E[f] and E[f^T M f] = <E[M], E[f f^T]>.
        part, atoms = ball(uniform), [(ball(w), v >> 3, v & 7) for v, w in extra.items()]
        gram_u = tuple(sum((g[k] for g in grams), arb(0)) / 32 for k in range(6))
        inverse_u = tuple(sum((n[k] for n in inverses), arb(0)) / 32 for k in range(6))
        offset_u = tuple(sum((f[k] for f in offs), arb(0)) / 8 for k in range(3))
        moment_u = tuple(sum((f[i] * f[j] for f in offs), arb(0)) / 8 for i, j in shape.PAIRS)
        mean_m = tuple(part * gram_u[k] + sum((w * grams[s][k] for w, s, _ in atoms), arb(0)) for k in range(6))
        mean_n = tuple(part * inverse_u[k] + sum((w * inverses[s][k] for w, s, _ in atoms), arb(0)) for k in range(6))
        mean_f = tuple(part * offset_u[k] + sum((w * offs[o][k] for w, _, o in atoms), arb(0)) for k in range(3))
        mixed_u = shape.sym_apply(gram_u, offset_u)
        mean_mf = tuple(part * mixed_u[k] + sum((w * shape.sym_apply(grams[s], offs[o])[k] for w, s, o in atoms), arb(0))
                        for k in range(3))
        mean_fmf = part * shape.contract(gram_u, moment_u) + sum((w * shape.quad(grams[s], offs[o]) for w, s, o in atoms), arb(0))

        middle = Centre(dom, limit)
        self.form = form = Form()
        self.counts = {"cross": 0, "same": 0, "secant": 0, "extinction": 0}
        # q*_m at the 32 shape vertices for all reciprocal pairs of the window, and the shape marginal of p
        duals = [m for m in term_window(cube) if lex_positive(m) and middle.dual(m) is not None]
        column = {m: k for k, m in enumerate(duals)}
        if duals:
            table = (arb_mat([[n[k] * DOUBLE[k] for k in range(6)] for n in inverses])
                     * arb_mat([[shape.moments(m)[k] for m in duals] for k in range(6)])).entries()
        marginal = [part / 32 + sum((w for w, s, _ in atoms if s == i), arb(0)) for i in range(32)]
        for m in term_window(cube):
            # cross-coset term F_r(q^x_m), q^x_m = |R(m+f)|^2
            if middle.cross(m) is not None:
                q = shape.quad(mean_m, m) + 2 * shape.dot(mean_mf, m) + mean_fmf
                value, slope = kernels.f_r(q, 1)
                form.constant += value - slope * q
                form.add_direct(slope, m, True)
                self.counts["cross"] += 1
            if not lex_positive(m):
                continue
            # same-coset pair 2 F_r(q_m)
            if middle.same(m) is not None:
                q = shape.quad(mean_m, m)
                value, slope = kernels.f_r(q, 1)
                form.constant += 2 * (value - slope * q)
                form.add_direct(2 * slope, m, False)
                self.counts["same"] += 1
            # reciprocal pair 2 w(m.f) F_d(q*_m)
            if m not in column:
                continue
            t_left, t_right = middle.phase_range(m)
            t_mid = (t_left + t_right) / 2
            q = shape.quad(mean_n, m)
            t_base = shape.dot(mean_f, m)
            chord = secant(t_left, t_right)
            half_integer = Fraction(round(t_mid - Fraction(1, 2))) + Fraction(1, 2)
            d = abs(t_mid - half_integer) + (t_right - t_left) / 2
            extinction = None
            if d <= Fraction(1, 2) and (chord is None or d <= Fraction(1, 5)):
                c_d = 2 * arb.pi() ** 2 if d == 0 else 2 * ((arb.pi() * ball(d)).sin() / ball(d)) ** 2
                k, count = column[m], len(duals)                  # average of 1/(c_d 2 F_d(q*)) over the vertices
                mean_inv = sum((marginal[i] * kernels.inv_f_d(table[i * count + k]) for i in range(32)), arb(0)) / (2 * c_d)
                zeta = t_base - ball(half_integer)
                u = zeta / mean_inv
                extinction = (u * zeta, u, half_integer, 1 / (2 * c_d))
            if chord is not None:
                p, slope_t = chord
                f_d, f_d1 = kernels.f_d(q, 1)
                phase = p * (slope_t * (t_base - ball(t_mid))).exp()
                value = 2 * f_d * phase
                if extinction is None or not extinction[0] > value:
                    dq, dt = 2 * f_d1 * phase, slope_t * value
                    form.constant += value - dq * q - dt * t_base
                    form.add_dual(dq, m)
                    form.add_phase(dt, m)
                    self.counts["secant"] += 1
                    continue
            if extinction is not None:
                _, u, half_integer, scale = extinction
                form.constant -= 2 * u * ball(half_integer)
                form.add_phase(2 * u, m)
                form.losses.append((m, u * u * scale))
                self.counts["extinction"] += 1
        if not sum(self.counts.values()):
            raise ArithmeticError("a tangent support needs at least one term")

    def energy_vertices(self, box):
        """Balls E(v) for the 256 vertices v of ``box``, with e >= min_v E(v) on the whole box:
        E = (T - 2 alpha - 2/alpha^2) / (2 l_2) with the separately concave T of Lemma 7.5(ii)."""
        self._check(box)
        scale = 2 * ell2()
        return [(value + self.kernels.constant) / scale for value in self.form.vertices(box, self.kernels)]

    def energy_lower(self, box, reduced=None):
        """E_- with e >= E_- on ``box``: the least lower endpoint of the vertex values (vertex principle)."""
        if reduced is not None:
            raise ValueError("the reduced variant is implemented for the other kinds of support")
        return minimum(self.energy_vertices(box))


class ExponentialSupport(Support):
    """An exponential support on the box ``dom`` (Lemma 7.5(iii)), valid on every box contained in ``dom``.

    Terms J as for ``TangentSupport``; the base points Q_j are the squared lengths at the centre of ``dom``.
    With s_j = -F_j'(Q_j)/F_j(Q_j):  W_j = F_j(Q_j), b_j = 0 for direct terms (twice that for a same-coset
    pair);  for a reciprocal pair whose phase interval on ``dom`` contains no point of Z + 1/2,
    W_j = 2 p_j F_d(Q_j) with p_j, b_j, t_{0,j} from (7.4); other reciprocal pairs are omitted.  Then

        2 l_2 e + 2 alpha + 2/alpha^2 >= M exp(U),   M = sum W_j,
        U = (1/M) sum_j W_j [ -s_j (q_j - Q_j) + b_j (t_j - t_{0,j}) ]   separately concave.
    """

    def __init__(self, dom, alpha, cube, limit):
        self._set_dom(dom)
        self.kernels = kernels = Kernels(alpha)
        middle = Centre(dom, limit)
        self.mass = arb(0)            # M
        self.form = form = Form()     # M * U
        self.lambda_e1 = None
        self.counts = {"cross": 0, "same": 0, "secant": 0}
        for m in term_window(cube):
            q_exact = middle.cross(m)
            if q_exact is not None:                                   # cross-coset term
                q = ball(q_exact)
                value, slope = kernels.f_r(q, 1)                      # W = F_r(Q), W s = -F_r'(Q)
                self.mass += value
                form.constant -= slope * q
                form.add_direct(slope, m, True)
                self.counts["cross"] += 1
            if not lex_positive(m):
                continue
            q_exact = middle.same(m)
            if q_exact is not None:                                   # same-coset pair
                q = ball(q_exact)
                value, slope = kernels.f_r(q, 1)
                self.mass += 2 * value
                form.constant -= 2 * slope * q
                form.add_direct(2 * slope, m, False)
                if m == (1, 0, 0):
                    self.lambda_e1 = -2 * slope                       # coefficient of q_{e_1} = r1^2 in Lambda
                self.counts["same"] += 1
            q_exact = middle.dual(m)
            if q_exact is None:
                continue
            t_left, t_right = middle.phase_range(m)
            chord = secant(t_left, t_right)
            if chord is None:
                continue
            p, slope_t = chord                                        # reciprocal pair with the chord of log w
            q = ball(q_exact)
            f_d, f_d1 = kernels.f_d(q, 1)
            weight = 2 * p * f_d
            self.mass += weight
            form.constant -= 2 * p * f_d1 * q + weight * slope_t * ball((t_left + t_right) / 2)
            form.add_dual(2 * p * f_d1, m)
            form.add_phase(weight * slope_t, m)
            self.counts["secant"] += 1
        if not self.mass > 0:
            raise ArithmeticError("an exponential support needs positive mass")

    def energy_lower(self, box, reduced=None):
        """E_- with e >= E_- on ``box`` (on its reduced points if ``reduced`` = (variant, rho) is given):
        (M exp(min_v U(v)) - 2 alpha - 2/alpha^2) / (2 l_2)."""
        self._check(box)
        shift = self.reduced_shift(*reduced, box) if reduced is not None else None
        lowest = minimum(self.form.vertices(box, self.kernels, shift))         # min_v M U(v)
        return lower((self.mass * (lowest / self.mass).exp() + self.kernels.constant) / (2 * ell2()))


def signed_triples(vectors):
    """Index triples i < j < k with v_i +- v_j +- v_k = 0  (for (7.6))."""
    index = {v: i for i, v in enumerate(vectors)}
    found = set()
    for i, a in enumerate(vectors):
        for j in range(i + 1, len(vectors)):
            b = vectors[j]
            for c in (tuple(x + y for x, y in zip(a, b)), tuple(x - y for x, y in zip(a, b))):
                for candidate in (c, tuple(-x for x in c)):
                    k = index.get(candidate)
                    if k is not None and k > j:
                        found.add((i, j, k))
    return sorted(found)


class VertexMaxSupport(Support):
    """A support on the box ``dom`` with constant phase bounds and base points at the vertex maxima.

    Terms J as for ``TangentSupport``.  Base point Q_j: an upper bound for the maximum of the squared
    length over the vertices of ``dom``.  A reciprocal pair +-m has the weight omega = the phase floor of m
    on ``dom`` (pairs with omega = 0 contribute nothing).
      form "tangent":      Lemma 7.5(ii)(a),  sum of omega [F(Q) + F'(Q)(q - Q)];
      form "exponential":  Lemma 7.5(iii) with W_j = omega_j F_j(Q_j), b_j = 0.
    With ``reserve`` the phase reserve of Lemma 7.5(iii') is added: triples of retained reciprocal pairs with
    m_i +- m_j +- m_k = 0 receive weights s_T >= 0, greedily, such that the weights of the triples through a
    pair do not exceed its capacity 2 F_d(sup q*) on ``dom``; rho = sum_T s_T (3/2 - sum omega)_+.  Any such
    allocation is admissible (floating point is used only to order the triples).
    """

    def __init__(self, dom, alpha, cube, limit, reserve=False, form="tangent"):
        if form not in ("tangent", "exponential"):
            raise ValueError("unknown form")
        self._set_dom(dom)
        self.exponential = form == "exponential"
        self.kernels = kernels = Kernels(alpha)
        middle = Centre(dom, limit)
        shapes = [tuple(map(ball, s)) for s in shape_vertices(dom)]
        offsets = [tuple(map(ball, f)) for f in offset_vertices(dom)]
        grams = [shape.gram(xi) for xi in shapes]
        inverses = [shape.gram_inverse(xi) for xi in shapes]
        self.mass = arb(0)
        self.form = out = Form()
        self.reserve = arb(0)
        self.lambda_e1 = None

        def largest(values):
            return greatest(upper(v) for v in values)

        dual = []                                                   # (m, omega, capacity)
        for m in term_window(cube):
            if middle.cross(m) is not None:                         # cross-coset term
                q = largest(shape.quad(g, tuple(a + b for a, b in zip(m, f))) for g in grams for f in offsets)
                value, slope = kernels.f_r(q, 1)
                self.mass += value
                out.constant += (0 if self.exponential else value) - slope * q
                out.add_direct(slope, m, True)
            if not lex_positive(m):
                continue
            if middle.same(m) is not None:                          # same-coset pair
                q = largest(shape.quad(g, m) for g in grams)
                value, slope = kernels.f_r(q, 1)
                self.mass += 2 * value
                out.constant += (0 if self.exponential else 2 * value) - 2 * slope * q
                out.add_direct(2 * slope, m, False)
                if m == (1, 0, 0):
                    self.lambda_e1 = -2 * slope
            if middle.dual(m) is not None:                          # reciprocal pair
                q = largest(shape.quad(n, m) for n in inverses)
                value, slope = kernels.f_d(q, 1)
                omega = phase_floor(*middle.phase_range(m))
                if omega > 0:
                    self.mass += 2 * omega * value
                    out.constant += (0 if self.exponential else 2 * omega * value) - 2 * omega * slope * q
                    out.add_dual(2 * omega * slope, m)
                capacity = lower(2 * value)                          # 2 F_d(sup q*) <= inf 2 F_d(q*) on dom
                if not (capacity.is_finite() and omega.is_finite()):
                    raise ArithmeticError("non-finite capacity of a reciprocal pair")
                dual.append((m, omega, capacity.max(arb(0))))
        if not self.mass > 0:
            raise ArithmeticError("a support needs positive mass")
        if reserve:
            remaining = [capacity for _, _, capacity in dual]
            candidates = []
            for triple in signed_triples([m for m, _, _ in dual]):
                gain = lower(arb(3) / 2 - sum((dual[i][1] for i in triple), arb(0)))
                if gain > 0:
                    candidates.append((float(gain * least(remaining[i] for i in triple)), triple, gain))
            candidates.sort(key=lambda row: (-row[0], row[1]))
            for _, triple, gain in candidates:
                stake = least(remaining[i] for i in triple)
                if not stake > 0:
                    continue
                for i in triple:
                    remaining[i] = lower(remaining[i] - stake).max(arb(0))
                self.reserve += gain * stake
            self.reserve = lower(self.reserve)

    def energy_lower(self, box, reduced=None):
        """E_- with e >= E_- on ``box`` (on its reduced points if ``reduced`` = (variant, rho) is given)."""
        self._check(box)
        shift = self.reduced_shift(*reduced, box) if reduced is not None else None
        lowest = minimum(self.form.vertices(box, self.kernels, shift))
        if self.exponential:
            lowest = lower(self.mass * (lowest / self.mass).exp())
        return lower((lowest + self.reserve + self.kernels.constant) / (2 * ell2()))


def partial_sum_lower(box, alpha, cube):
    """Energy rule (i), Lemma 7.5(i): E_- = (sum_j omega_j F_j(qbar_j) - 2 alpha - 2/alpha^2)/(2 l_2) <= e on the box.

    J = all terms of (7.2) with max|m_i| <= cube; qbar_j is the upper end of the interval value of the
    squared length over the box; omega_j = 1 for direct terms and the phase floor for reciprocal pairs.
    """
    kernels = Kernels(alpha)
    xi = tuple(hull(a, b) for a, b in zip(box[0][:5], box[1][:5]))
    f = tuple(hull(a, b) for a, b in zip(box[0][5:], box[1][5:]))

    def length(v):
        return upper(sum((sq(x) for x in v), arb(0)))

    total = arb(0)
    for m in term_window(cube):
        q = length(shape.real_vector(xi, tuple(a + b for a, b in zip(m, f))))
        if not q > 0:
            raise ArithmeticError("a squared length without positive upper bound")
        total += kernels.f_r(q)[0]
        if not lex_positive(m):
            continue
        total += 2 * kernels.f_r(length(shape.real_vector(xi, m)))[0]
        omega = phase_floor(*phase_range(m, box[0][5:], box[1][5:]))
        if omega > 0:
            total += 2 * omega * kernels.f_d(length(shape.dual_vector(xi, m)))[0]
    return lower((total + kernels.constant) / (2 * ell2()))
