"""Ball arithmetic helpers, the constants of the paper and the kernels of the screened series.

Every real number is represented by a ball (python-flint ``arb``); an inequality is accepted only if it
holds for the whole ball (Section 9.1 of the paper).  Exact data are ``fractions.Fraction``.
"""

from fractions import Fraction

from flint import arb, ctx, fmpq

# ---------------------------------------------------------------------------------------------
# Constants taken as given (Proposition 2.7; enclosures printed in Section 9.2 of the paper).
# ---------------------------------------------------------------------------------------------
E_B_LOWER = Fraction("-0.89592925568176528916624546293829460538061046722070")
E_B_UPPER = E_B_LOWER + Fraction(4, 10**50)
E_F_LOWER = Fraction("-0.89587361519510845989748779611028534450181510608894")
E_F_UPPER = E_F_LOWER + Fraction(4, 10**50)
GAP_UPPER = E_F_UPPER - E_B_LOWER  # g^+ >= g = e_F - e_B  (Section 7.1)


def set_precision(bits):
    """Working precision in bits; one arithmetic thread."""
    ctx.prec = bits
    ctx.threads = 1


def ball(x):
    """A ball containing the exact rational (or integer) x; balls are returned unchanged."""
    if isinstance(x, arb):
        return x
    if isinstance(x, int):
        return arb(x)
    x = Fraction(x)
    return arb(fmpq(x.numerator, x.denominator))


def lower(x):
    """An exact number that is not larger than any point of the ball x."""
    return x.lower()


def upper(x):
    """An exact number that is not smaller than any point of the ball x."""
    return x.upper()


def hull(a, b):
    """A ball containing the closed interval between the exact rationals a <= b."""
    return ball(a) if a == b else ball(a).union(ball(b))


def interval(lo_ball, hi_ball):
    """A ball containing every number between a lower and an upper bound given as balls."""
    return lower(lo_ball).union(upper(hi_ball))


def sq(x):
    """Tight enclosure of the squares of the points of the ball x."""
    small, large = x.abs_lower(), x.abs_upper()
    return (small * small).union(large * large)


def pos_part(x):
    """Enclosure of max(x, 0)."""
    return x.max(arb(0))


def finite(*values):
    return all(v.is_finite() for v in values)


def least(values):
    """The smallest of some exact numbers.  Python's ``min`` skips a NaN that is not the first element, so a
    non-finite value is an error here (and the leaf is rejected)."""
    values = list(values)
    if not values or not all(v.is_finite() for v in values):
        raise ArithmeticError("non-finite value")
    return min(values)


def greatest(values):
    """The largest of some exact numbers; a non-finite value is an error."""
    values = list(values)
    if not values or not all(v.is_finite() for v in values):
        raise ArithmeticError("non-finite value")
    return max(values)


def pi():
    return arb.pi()


def ell2():
    """l_2 = (8 pi / 3)^(1/3), Section 2.2."""
    return (8 * arb.pi() / 3).root(3)


def e_b_upper():
    return ball(E_B_UPPER)


def e_f_upper():
    return ball(E_F_UPPER)


def gap_upper():
    return ball(GAP_UPPER)


# ---------------------------------------------------------------------------------------------
# The functions G(a, t) of (2.5):  G(1/2, t) = sqrt(pi/t) erfc(sqrt t),  G(1, t) = exp(-t)/t,
# G(a+1, t) = (exp(-t) + a G(a, t)) / t   (Section 9.1).
# ---------------------------------------------------------------------------------------------
def gamma_ladder(a, t, order):
    """[G(a, t), G(a+1, t), ..., G(a+order, t)] for a in {1/2, 1} and a ball t > 0."""
    if not t > 0:
        raise ArithmeticError("the argument of G must be positive on the whole ball")
    decay = (-t).exp()
    if a == Fraction(1, 2):
        value = (arb.pi() / t).sqrt() * t.sqrt().erfc()
    elif a == 1:
        value = decay / t
    else:
        raise ValueError("a must be 1/2 or 1")
    values = [value]
    for k in range(order):
        value = (decay + ball(a + k) * value) / t
        values.append(value)
    return values


class Kernels:
    """The kernels F_r, F_d of the screened series (7.2) for one value of alpha, and their derivatives.

    F_r(q) = alpha G(1/2, pi alpha^2 q),  F_r^(k)(q) = (-pi)^k alpha^(2k+1) G(1/2+k, pi alpha^2 q)   (C.1)
    F_d(q) = alpha^-2 G(1, pi q/alpha^2) = exp(-pi q/alpha^2)/(pi q),  F_d' = -(pi/alpha^2 + 1/q) F_d   (C.1)
    """

    def __init__(self, alpha):
        self.alpha_exact = Fraction(alpha)
        if not self.alpha_exact > 0:
            raise ValueError("the screened series (7.2) needs alpha > 0")
        self.alpha = ball(alpha)
        self.rate_r = arb.pi() * self.alpha**2
        self.rate_d = arb.pi() / self.alpha**2
        # the constant -2 alpha - 2/alpha^2 of (7.2)
        self.constant = -2 * self.alpha - 2 / self.alpha**2

    def f_r(self, q, order=0):
        """[F_r(q), F_r'(q), ..., F_r^(order)(q)]."""
        ladder = gamma_ladder(Fraction(1, 2), self.rate_r * q, order)
        return [(-arb.pi()) ** k * self.alpha ** (2 * k + 1) * g for k, g in enumerate(ladder)]

    def f_d(self, q, order=0):
        """[F_d(q), F_d'(q)] (order at most 1)."""
        value = (-self.rate_d * q).exp() / (arb.pi() * q)
        if order == 0:
            return [value]
        if order == 1:
            return [value, -(self.rate_d + 1 / q) * value]
        raise ValueError("only F_d and F_d' are used")

    def inv_f_d(self, q):
        """1/F_d(q) = pi q exp(pi q/alpha^2), increasing and convex in q (proof of Lemma 7.5(ii))."""
        return arb.pi() * q * (self.rate_d * q).exp()
