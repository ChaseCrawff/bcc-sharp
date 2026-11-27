"""Anchor rules (Section 7.7) with the planar gain: the positivity tests of Lemma C.6 and the
comparisons of Lemmas 7.12 and C.12.

For f0 in (1/2)Z^3 \\ Z^3 and n in Z^3, with delta = f - f0 - n and h = R(xi) delta, two estimates

    e(xi, f) - e(xi, f0) >= E(xi, delta),        D(xi, f) - D(xi, f0) <= D(xi, delta)          (7.10)

give Def(xi, f) - Def(xi, f0) >= E - g^+ D.  Here E is a quadratic form with an interval matrix
(Lemma C.10) and D = gamma |h|^2 (Lemma C.5).
"""

from fractions import Fraction
from itertools import product

from flint import arb

from . import defect, shape
from .balls import ball, e_b_upper, e_f_upper, gap_upper, hull, least, lower, pos_part, sq, upper
from .jets import ldl_pivots, one_variable_minimum
from .gain import GainForm
from .planar import AnchorEnergy, PlanarGain

HALF = Fraction(1, 2)


def exact_fraction(x):
    """The exact rational value of a ball of radius zero."""
    if not x.is_exact():
        raise ValueError("an exact number is required")
    mantissa, exponent = x.man_exp()
    return Fraction(int(mantissa)) * Fraction(2) ** int(exponent)


# ---------------------------------------------------------------------------------------------
# Lemma C.6: positivity tests for a symmetric 3x3 matrix [P] of intervals on a box Omega
# ---------------------------------------------------------------------------------------------
def sign_sectors(lo, hi):
    """The sign vectors s with Omega_s nonempty that are needed to cover Omega = prod [lo_i, hi_i],
    each with the ranges of y_i = |delta_i| on Omega_s.  (A coordinate interval [a, 0] with a < 0 is
    covered by the sector s_i = -1 alone.)"""
    options = []
    for a, b in zip(lo, hi):
        choices = []
        if a < 0:
            choices.append((-1, max(Fraction(0), -b), -a))
        if b > 0 or a >= 0:
            choices.append((1, max(Fraction(0), a), b))
        options.append(choices)
    for sector in product(*options):
        signs, lows, highs = zip(*sector)
        yield signs, lows, highs


def sector_matrix(matrix, signs):
    """P^s: the exact lower endpoints of the intervals s_i s_j [P]_ij  (Lemma C.6)."""
    return tuple(tuple(lower(matrix[i][j] * (signs[i] * signs[j])) for j in range(3)) for i in range(3))


def drop_positive_offdiagonal(matrix):
    """check-P^s: P^s with its positive off-diagonal entries replaced by 0  (Lemma C.6)."""
    return tuple(tuple(v if i == j else v.min(arb(0)) for j, v in enumerate(row)) for i, row in enumerate(matrix))


def definite_witness(matrix, lo, hi):
    """Tests (i) and (ii) of Lemma C.6.  Returns the least lower endpoint of a pivot, a positive exact
    number, if delta^T P delta >= c |delta|^2 with some c > 0 for all P in [P] and all delta in Omega
    (in case (i): for all delta in R^3); otherwise None.
    """
    pivots = ldl_pivots(matrix)                                   # (i) interval factorization
    if pivots is not None:
        return least(lower(v) for v in pivots)
    witnesses = []
    for signs, _, _ in sign_sectors(lo, hi):                      # (ii) sign sectors
        pivots = ldl_pivots(drop_positive_offdiagonal(sector_matrix(matrix, signs)))
        if pivots is None:
            return None
        witnesses.append(least(lower(v) for v in pivots))
    return least(witnesses)


def _box_floor(q, lows, highs):
    """Test (iii): the bound (5.5) for psi(y) = y^T Q y on the box prod [lows_i, highs_i], Q exact."""
    centre = [ball((a + b) / 2) for a, b in zip(lows, highs)]
    radii = [upper(ball((b - a) / 2)) for a, b in zip(lows, highs)]
    gradient = [2 * sum((q[i][j] * centre[j] for j in range(3)), arb(0)) for i in range(3)]
    value = sum((q[i][j] * centre[i] * centre[j] for i in range(3) for j in range(3)), arb(0))
    for i in range(3):
        if not radii[i] > 0:
            continue
        coupling = sum((2 * q[i][j].abs_upper() * radii[j] for j in range(3) if j != i), arb(0))
        kappa = lower(2 * q[i][i] - coupling / radii[i])
        value += one_variable_minimum(upper(gradient[i].abs_upper()), kappa, radii[i])
    return lower(value)


def _schur_floor(q, lows):
    """Test (iv): for a coordinate i with y_i >= l > 0, the bound varsigma l^2 with the Schur complement
    varsigma of the block of the other two coordinates in check-P^s."""
    best = None
    for i in range(3):
        if not lows[i] > 0:
            continue
        j, k = (a for a in range(3) if a != i)
        a, b, c = q[j][j], q[j][k], q[k][k]
        v, w = q[i][j], q[i][k]
        determinant = a * c - b * b
        if not (a > 0 and determinant > 0):
            continue
        reduced = q[i][i] - (c * v * v + a * w * w - 2 * b * v * w) / determinant
        if reduced >= 0:
            bound = lower(reduced * sq(ball(lows[i])))
            best = bound if best is None else best.max(bound)
    return best


def form_floor(matrix, lo, hi):
    """J of Section C.3: an exact number with delta^T P delta >= J for all P in [P] and delta in Omega;
    on every sign sector the largest of the interval value of y^T P^s y, of test (iii) for P^s and of
    test (iv) for check-P^s is taken, and J is the least of these over the sectors."""
    floors = []
    for signs, lows, highs in sign_sectors(lo, hi):
        p_s = sector_matrix(matrix, signs)
        y = [hull(a, b) for a, b in zip(lows, highs)]
        direct = sum((p_s[i][i] * sq(y[i]) for i in range(3)), arb(0))
        direct += sum((2 * p_s[i][j] * y[i] * y[j] for i in range(3) for j in range(i + 1, 3)), arb(0))
        best = lower(direct).max(_box_floor(p_s, lows, highs))
        schur = _schur_floor(drop_positive_offdiagonal(p_s), lows)
        floors.append(best if schur is None else best.max(schur))
    return least(floors)


def subtract(matrix, factor, other):
    return tuple(tuple(a - factor * b for a, b in zip(row, row2)) for row, row2 in zip(matrix, other))


# ---------------------------------------------------------------------------------------------
# Anchors with the planar gain
# ---------------------------------------------------------------------------------------------
class PlanarAnchorData:
    """Everything that depends only on the shape box S and the half class f0 (f_{0,3} in 1/2 + Z)."""

    def __init__(self, lo, hi, f0):
        self.lo, self.hi = tuple(lo), tuple(hi)
        self.gain = PlanarGain(lo, hi, f0)
        self.f0 = self.gain.f0
        self.growth = defect.AnchorDefect(lo, hi, self.f0)
        self._energy = None

    def energy(self):
        if self._energy is None:
            self._energy = AnchorEnergy(self.lo, self.hi, self.f0)
        return self._energy


class PlanarComparison:
    """The data of Lemma C.10 for one box B = S x O and one n: the box of (v, t), the matrix [L]/(2 l_2),
    the coefficient gamma of Lemma C.5 and the matrix [L]/(2 l_2) - g^+ gamma diag(A_par^T A_par, c^2)."""

    def __init__(self, data, box, n):
        if len(n) != 3 or any(type(k) is not int for k in n):
            raise ValueError("n must be an integer vector")
        lo, hi = box
        if tuple(lo[:5]) != data.lo or tuple(hi[:5]) != data.hi:
            raise ValueError("shape box mismatch")
        d_lo = tuple(a - f - k for a, f, k in zip(lo[5:], data.f0, n))
        d_hi = tuple(b - f - k for b, f, k in zip(hi[5:], data.f0, n))
        self.eta = max(abs(d_lo[2]), abs(d_hi[2]))                      # |t| <= eta
        if not self.eta < HALF:
            raise ValueError("the planar gain needs |delta_3| < 1/2")
        delta = tuple(hull(a, b) for a, b in zip(d_lo, d_hi))
        sigma = data.gain.sigma
        v = (delta[0] + sigma[0] * delta[2], delta[1] + sigma[1] * delta[2])      # v = delta_par + t sigma
        self.left = tuple(exact_fraction(lower(x)) for x in v) + (d_lo[2],)
        self.right = tuple(exact_fraction(upper(x)) for x in v) + (d_hi[2],)
        rho = tuple(max(abs(a), abs(b)) for a, b in zip(self.left, self.right))
        self.matrix = data.gain.matrix(rho[0], rho[1], self.eta)
        h2 = defect.squared_norm(shape.real_vector(data.growth.xi, delta))        # |h|^2 on S x Omega
        self.gamma = data.growth.gamma(delta, pos_part(lower(h2)), upper(h2))
        self.surplus = subtract(self.matrix, gap_upper() * self.gamma, data.gain.metric)


def decide(gain_matrix, surplus, left, right, d0_minus):
    """The three comparisons of Lemma 7.12 for the interval matrices [G] >= energy gain and
    [P] = [G] - g^+ gamma [metric] on the box prod [left_i, right_i]:
      * P positive definite by test (i) or (ii) of Lemma C.6   =>  (A)   (Lemma 7.12(i));
      * J(P) > 0                                               =>  (D)   (Lemma 7.12(ii) with s_- = 0);
      * J(G) > g^+ (1 - D_0^-)                                 =>  (E)   (Lemma 7.12(iii)).
    Returns (condition, margin) or None.
    """
    pivot = definite_witness(surplus, left, right)
    if pivot is not None and pivot > 0:
        return "A", pivot
    floor = form_floor(surplus, left, right)
    if floor.is_finite() and floor > 0:
        return "D", floor
    floor = form_floor(gain_matrix, left, right)
    above = lower(floor - gap_upper() * (1 - d0_minus))
    if above.is_finite() and above > 0:
        return "E", above
    return None


def rule_anchor_planar(data, box, n):
    """Anchor rules of Lemma 7.12 with the planar gain (Lemmas C.10, C.5, C.6), in the coordinates (v, t)."""
    comparison = PlanarComparison(data, box, n)
    return decide(comparison.matrix, comparison.surplus, comparison.left, comparison.right, data.growth.d0_minus)


class GainAnchorData:
    """What depends only on the shape box S and the half class f0 for the gain form of Lemma C.3."""

    def __init__(self, lo, hi, f0):
        self.lo, self.hi = tuple(lo), tuple(hi)
        self.gain = GainForm(lo, hi, f0)
        self.f0 = self.gain.f0
        self.growth = defect.AnchorDefect(lo, hi, self.f0)


def gain_comparison(data, box, n):
    """For the gain form of Lemma C.3 on B = S x O: the box of delta = f - f0 - n, the matrix [H] and the
    matrix [H] - g^+ gamma [M], with rho_i = sup |delta_i|, h_+^2 = sup |R delta|^2 and gamma from Lemma C.5."""
    if len(n) != 3 or any(type(k) is not int for k in n):
        raise ValueError("n must be an integer vector")
    lo, hi = box
    if tuple(lo[:5]) != data.lo or tuple(hi[:5]) != data.hi:
        raise ValueError("shape box mismatch")
    left = tuple(a - f - k for a, f, k in zip(lo[5:], data.f0, n))
    right = tuple(b - f - k for b, f, k in zip(hi[5:], data.f0, n))
    rho = tuple(max(abs(a), abs(b)) for a, b in zip(left, right))
    delta = tuple(hull(a, b) for a, b in zip(left, right))
    h2 = defect.squared_norm(shape.real_vector(data.growth.xi, delta))
    matrix = data.gain.matrix(rho, upper(h2))
    gamma = data.growth.gamma(delta, pos_part(lower(h2)), upper(h2))
    surplus = subtract(matrix, gap_upper() * gamma, data.gain.metric)
    return left, right, matrix, surplus


def rule_anchor_slack(data, box, n, support):
    """Anchor rule (ii), Lemma 7.12(ii), with the gain form of Lemma C.3:

        s_- + J(P) > 0,   P = [H] - g^+ gamma [M],   J from Lemma C.6,

    where s_- <= Def(xi, f0) on S is  max{0, E_- - e_B^+ - g^+ D_0^+}:  E_- is the lower bound of the given
    support for the energy of the anchor on S x {f0 + n} (Lemma 7.5), and D_0^+ >= D(xi, f0) on S is the
    least d^+ < 1 over the registrations of the list with half class f0 (then D(xi, f0) = d_0 <= d^+ by
    Lemma 7.8(v)), or 1.  Gives (D).  Returns (condition, margin) or None.
    """
    left, right, _, surplus = gain_comparison(data, box, n)
    lo, hi = box
    anchor_point = tuple(f + k for f, k in zip(data.f0, n))
    anchor_box = (tuple(lo[:5]) + anchor_point, tuple(hi[:5]) + anchor_point)
    bounds = [e[1] for e in data.growth.entries if e[1] is not None and e[1] < 1]
    d0_plus = least(bounds) if bounds else arb(1)
    slack = lower(support.energy_lower(anchor_box) - e_b_upper() - gap_upper() * d0_plus).max(arb(0))
    margin = lower(slack + form_floor(surplus, left, right))
    if margin.is_finite() and margin > 0:
        return "D", margin
    return None


def rule_anchor_gain(data, box, n):
    """Anchor rules of Lemma 7.12 with the energy-gain form of Lemma C.3 (gain (ii)), Lemmas C.5 and C.6,
    in the coordinates delta = f - f0 - n, with rho_i = sup |delta_i| and h_+^2 = sup |R delta|^2 on the box."""
    left, right, matrix, surplus = gain_comparison(data, box, n)
    return decide(matrix, surplus, left, right, data.growth.d0_minus)


def rule_anchor_centred(data, box, n, registration=None):
    """The centred tests of Lemma C.12, with E_0^- from Lemma C.11.

      (i)   E_0^- + J^- > e_F^+                                  =>  (E)
      (ii)  E_0^- + J^- - e_B^+ - g^+ D^+ > 0                    =>  (D),  D^+ from ``registration`` (Lemma 7.8(ii))
      (iii) s_- + J(P) > 0                                       =>  (D),  P as in ``rule_anchor_planar``,
            s_- = max{0, E_0^- - e_B^+ - g^+ D_0^+, inf_S[(A_0 - R_4(1/2))/(2 l_2) - 28 g^+ |C - I|_F^2] - e_B^+}.
    Returns (condition, margin) or None.
    """
    comparison = PlanarComparison(data, box, n)
    energy = data.energy()
    e0 = energy.energy_floor()
    gain = form_floor(comparison.matrix, comparison.left, comparison.right)
    total = lower(e0 + gain)
    above = lower(total - e_f_upper())
    if above.is_finite() and above > 0:
        return "E", above
    if registration is not None:
        d_plus = defect.defect_upper(box, registration)
        if d_plus is not None:
            margin = lower(total - e_b_upper() - gap_upper() * d_plus)
            if margin.is_finite() and margin > 0:
                return "D", margin
    # s_-: a lower bound for the deficit of the anchor on S
    slack = arb(0)
    entries = [e for e in data.growth.entries if e[1] is not None and e[1] < 1]
    if entries:                                   # D(xi, f0) = d_0 <= d^+ where d^+ < 1 (Lemma 7.8(v))
        d0_plus = least(e[1] for e in entries)
        slack = slack.max(lower(e0 - e_b_upper() - gap_upper() * d0_plus))
    w = data.growth.closest_frame()
    if w is not None:                             # D(xi, f0) <= 28 |C - I|_F^2 (Lemma 7.8(v))
        slack = slack.max(lower(energy.deficit_floor(w, gap_upper()) - e_b_upper()))
    floor = form_floor(comparison.surplus, comparison.left, comparison.right)
    margin = lower(slack + floor)
    if margin.is_finite() and margin > 0:
        return "D", margin
    return None
