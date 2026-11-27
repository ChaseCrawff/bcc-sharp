"""The rules: for one box and one leaf of the certificate, decide whether the box is discharged.

Every function returns a pair (condition, margin): ``condition`` is the condition of Definition 7.1 that
has been established ('E', 'D', 'A' or 'N'), and ``margin`` is an exact positive number, the lower
endpoint of the quantity whose positivity was proved.  A rule that cannot be established raises
``Rejected``.
"""

from fractions import Fraction

from . import anchor, defect, planar
from .balls import ball, e_b_upper, e_f_upper, ell2, gap_upper, lower
from .energy import TangentSupport, minimum, partial_sum_lower


class Rejected(Exception):
    """The leaf does not prove its box discharged."""


class Unproved(Rejected):
    """The hypotheses of the rule hold, but its inequality could not be established on the whole box."""


def _positive(value, text):
    if not value.is_finite() or not value > 0:
        raise Unproved(text)
    return value


def rule_e(box, support, reduced=None):
    """Energy rules (ii), (iii) and (iv) of Lemma 7.5: the lower bound E_- of a support exceeds e_F^+.
    Gives (E): e > e_F on the box; with ``reduced`` = (variant, rho) (Lemma 7.5(iv)), on its reduced points.
    """
    try:
        value = support.energy_lower(box, reduced)
    except ValueError as error:
        raise Rejected(str(error))
    return "E", _positive(lower(value - e_f_upper()), "support not above the FCC energy")


def rule_slabs(box, slabs, inner):
    """Lemma 7.2(iii): slabs {kappa_i <= a} or {kappa_i >= a} along shape coordinates that satisfy (N) are
    removed one after the other, and the rule ``inner`` (a function of a box) is applied to the remaining box.
    Each slab is [axis, side, a, kind, m]: side 0 removes {kappa_axis <= a}, side 1 removes {kappa_axis >= a};
    (kind, m) is the witness of (N) for the slab (``rule_n``)."""
    lo, hi = box
    for axis, side, value, kind, m in slabs:
        value = Fraction(value)
        if type(axis) is not int or not 0 <= axis <= 4 or side not in (0, 1) or not lo[axis] < value < hi[axis]:
            raise Rejected("invalid slab")
        if side == 0:
            slab = (lo, hi[:axis] + (value,) + hi[axis + 1:])
            lo = lo[:axis] + (value,) + lo[axis + 1:]
        else:
            slab = (lo[:axis] + (value,) + lo[axis + 1:], hi)
            hi = hi[:axis] + (value,) + hi[axis + 1:]
        rule_n(slab, kind, tuple(m))
    return inner((lo, hi))


def rule_d1(box, support, registration):
    """Deficit rule (i), Lemma 7.9(i):  E_- - e_B^+ - g^+ D_+ > 0, with E_- from Lemma 7.5 (ii) or (iii) and
    D_+ < 1 from Lemma 7.8(ii) for the given registration.  Gives (D).
    """
    d_plus = defect.defect_upper(box, registration)
    if d_plus is None:
        raise Unproved("the registration gives no upper bound below one for the defect")
    return "D", _positive(lower(support.energy_lower(box) - e_b_upper() - gap_upper() * d_plus),
                          "deficit rule (i) fails")


def rule_d3(box, support, registration, quaternion, numerator):
    """Deficit rule (ii), Lemma 7.9(ii) (joint vertex rule):

        min_v [ E(v) - e_B^+ - g^+ (1 - t + t C(v)) ] > 0,     t = numerator/4096 in [0, 1],

    E the separately concave energy bound and C the separately convex majorant of the trial cost for
    the rotation U, both evaluated at the same 256 vertices v.  Gives (D).
    """
    if type(numerator) is not int or not 0 <= numerator <= 4096:
        raise Rejected("t must be k/4096 with 0 <= k <= 4096")
    t = ball(Fraction(numerator, 4096))
    cost = defect.cost_vertices(box, registration, defect.rotation_from_quaternion(quaternion))
    if cost is None:
        raise Rejected("convexity condition of the strain term fails")
    if not isinstance(support, TangentSupport):
        raise Rejected("the joint vertex rule needs a tangent support")
    energy = support.energy_vertices(box)
    e_b, gap = e_b_upper(), gap_upper()
    values = [e - e_b - gap * (1 - t + t * c) for e, c in zip(energy, cost)]
    return "D", _positive(minimum(values), "joint vertex rule fails")


def rule_pf(box, shift, eta):
    """Planar rule (ii), Lemma 7.7(ii) with the fibre bound of Lemma C.8 and Remark C.9:
    after the translation f_3 -> f_3 - shift (Lemma 7.2(ii)), |f_3 - 1/2| <= eta < 1/2 on the box, and the
    lower bound for 2 l_2 e, valid for all f_par, exceeds 2 l_2 e_F^+.  Gives (E).
    """
    eta = Fraction(eta)
    if type(shift) is not int or not 0 <= eta < Fraction(1, 2):
        raise Rejected("invalid band")
    lo, hi = box
    centre_height = shift + Fraction(1, 2)
    if lo[7] < centre_height - eta or hi[7] > centre_height + eta:
        raise Rejected("the box leaves the band |f_3 - 1/2| <= eta")
    bound = planar.fibre_bound(lo[:5], hi[:5], eta)
    if bound is None:
        raise Rejected("hypotheses of the fibre bound fail")
    return "E", _positive(lower(bound / (2 * ell2()) - e_f_upper()), "fibre bound not above the FCC energy")


_ANCHOR_DATA = {}


def _anchor_data(box, f0):
    key = (box[0][:5], box[1][:5], tuple(f0))
    if key not in _ANCHOR_DATA:
        if len(_ANCHOR_DATA) > 256:
            _ANCHOR_DATA.clear()
        _ANCHOR_DATA[key] = anchor.PlanarAnchorData(box[0][:5], box[1][:5], f0)
    return _ANCHOR_DATA[key]


def rule_ap(box, f0, n):
    """Anchor rule with the planar gain (Lemma 7.12 (i), (ii) or (iii); Lemmas C.10, C.5, C.6)."""
    f0 = tuple(Fraction(v) for v in f0)
    try:
        result = anchor.rule_anchor_planar(_anchor_data(box, f0), box, tuple(n))
    except ValueError as error:
        raise Rejected(str(error))
    if result is None:
        raise Unproved("no test of the anchor rule with the planar gain succeeds")
    return result


def rule_ac(box, f0, n, registration=None):
    """Centred tests about an anchor (Lemma C.12 with Lemmas C.10 and C.11)."""
    f0 = tuple(Fraction(v) for v in f0)
    try:
        result = anchor.rule_anchor_centred(_anchor_data(box, f0), box, tuple(n), registration)
    except ValueError as error:
        raise Rejected(str(error))
    if result is None:
        raise Unproved("no centred test succeeds")
    return result


_GAIN_DATA = {}


def _gain_data(box, f0):
    key = (box[0][:5], box[1][:5], f0)
    if key not in _GAIN_DATA:
        if len(_GAIN_DATA) > 256:
            _GAIN_DATA.clear()
        _GAIN_DATA[key] = anchor.GainAnchorData(box[0][:5], box[1][:5], f0)
    return _GAIN_DATA[key]


def rule_ag(box, f0, n):
    """Anchor rule with the energy-gain form of Lemma C.3 (Lemma 7.12 (i), (ii) or (iii); Lemmas C.5, C.6)."""
    f0 = tuple(Fraction(v) for v in f0)
    try:
        result = anchor.rule_anchor_gain(_gain_data(box, f0), box, tuple(n))
    except ValueError as error:
        raise Rejected(str(error))
    if result is None:
        raise Unproved("no test of the anchor rule with the energy-gain form succeeds")
    return result


def rule_as(box, f0, n, support):
    """Anchor rule (ii) with the energy-gain form of Lemma C.3 and a positive lower bound s_- for the deficit
    of the anchor obtained from a support (Lemma 7.12(ii); Lemmas 7.5, 7.8(v), C.3, C.5, C.6)."""
    f0 = tuple(Fraction(v) for v in f0)
    try:
        result = anchor.rule_anchor_slack(_gain_data(box, f0), box, tuple(n), support)
    except ValueError as error:
        raise Rejected(str(error))
    if result is None:
        raise Unproved("anchor rule (ii) with the energy-gain form fails")
    return result


def rule_n(box, kind, m):
    """(N) of Definition 7.1: the box contains no reduced point, because (4.2) or (4.3) is violated strictly on
    the whole shape box for the fixed integer vector m.  Exact rational arithmetic.

    kind "full":  sup |R m|^2 / r1^2 < 1  with
        |R m|^2 / r1^2 = (m1 + x m2 + y m3)^2 + (r2/r1)^2 (m2 + z m3)^2 + m3^2 / (r1^4 r2^2);
    kind "projected":  sup [ (m2 + z m3)^2 + m3^2 / (r1^2 r2^4) ] < 1, i.e. (4.3) for (m2, m3).
    The suprema are exact: each expression is convex in r2^2 and decreasing in r1, and the squares of the
    affine functions of x, y, z are largest at an end of their ranges.
    """
    if len(m) != 3 or any(type(k) is not int for k in m):
        raise Rejected("an integer vector is required")
    lo, hi = box
    r1, r2 = lo[0], lo[1]

    def square_max(low, high):
        return max(low * low, high * high)

    b_low = m[1] + min(lo[4] * m[2], hi[4] * m[2])
    b_high = m[1] + max(lo[4] * m[2], hi[4] * m[2])
    b2 = square_max(b_low, b_high)
    if kind == "projected":
        if (m[1], m[2]) == (0, 0):
            raise Rejected("(m2, m3) must not vanish")
        value = b2 + Fraction(m[2] * m[2]) / (r1 * r1 * r2 ** 4)
    elif kind == "full":
        if tuple(m) == (0, 0, 0):
            raise Rejected("m must not vanish")
        a_low = m[0] + min(lo[2] * m[1], hi[2] * m[1]) + min(lo[3] * m[2], hi[3] * m[2])
        a_high = m[0] + max(lo[2] * m[1], hi[2] * m[1]) + max(lo[3] * m[2], hi[3] * m[2])
        a2 = square_max(a_low, a_high)
        value = max(a2 + (s / r1) ** 2 * b2 + Fraction(m[2] * m[2]) / (r1 ** 4 * s * s) for s in (lo[1], hi[1]))
    else:
        raise Rejected("unknown kind of reduction witness")
    if not value < 1:
        raise Unproved("the reduction inequality is not violated on the whole box")
    return "N", ball(1 - value)


def rule_e1(box, alpha, cube):
    """Energy rule (i), Lemma 7.5(i): the partial sum over max|m_i| <= cube with interval bounds exceeds e_F^+."""
    if type(cube) is not int or not 1 <= cube <= 4:
        raise Rejected("invalid cube")
    value = partial_sum_lower(box, Fraction(alpha), cube)
    return "E", _positive(lower(value - e_f_upper()), "partial sum not above the FCC energy")


def rule_pl(box):
    """Planar rule (i), Lemma 7.7(i) with Montgomery's theorem: the lower bound for 2 l_2 e exceeds 2 l_2 e_F^+."""
    bound = planar.layer_bound(box)
    if bound is None:
        raise Rejected("the box does not lie in a band eta <= f_3 <= 1 - eta")
    return "E", _positive(lower(bound / (2 * ell2()) - e_f_upper()), "planar bound not above the FCC energy")
