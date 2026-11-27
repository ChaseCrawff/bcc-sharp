"""Rigorous helpers on top of python-flint arb.

* Rigorous decimal output of an arb enclosure (exact integer arithmetic, no float rounding).
* Rigorous upper bounds for Gaussian tail integrals and for lattice-sum tails.

Lattice-sum tail lemma (used for every truncated sum in this package)
--------------------------------------------------------------------
Let P subset R^3 have minimum separation >= 2*rho (e.g. any translate of a lattice whose
shortest nonzero vector has length >= 2*rho). The balls B(p, rho), p in P, are disjoint, so
    N(r) := #{p in P : |p| <= r} <= B(r) := ((r + rho)/rho)^3.
Let g >= 0 be C^1 and decreasing on [R, inf) with r^3 g(r) -> 0. Stieltjes integration by parts
(twice) gives
    sum_{p in P, |p| > R} g(|p|) = -g(R) N(R) + int_R^inf N(r) (-g'(r)) dr
                                 <= B(R) g(R) + int_R^inf B'(r) g(r) dr,
with B'(r) = 3 (r + rho)^2 / rho^3 <= (3/rho^3) (1 + rho/R)^2 r^2 for r >= R.
For g(r) = C r^{-j} exp(-a r^2) this yields `lattice_tail_bound` below.

Gaussian tail integrals: for a > 0, R > 0,
    k <= 0:              int_R^inf r^k e^{-a r^2} dr <= R^k e^{-a R^2} / (2 a R)
    k > 0, 2 a R^2 > k:  int_R^inf r^k e^{-a r^2} dr <= R^k e^{-a R^2} / (2 a R - k/R)
(the second by concavity of k log r - a r^2). Also erfc(x) <= e^{-x^2} / (x sqrt(pi)), x > 0.
"""

from flint import arb, fmpz


def arb_of(x):
    """arb from int / Fraction / arb (exact for rationals up to working precision)."""
    from fractions import Fraction
    if isinstance(x, arb):
        return x
    if isinstance(x, Fraction):
        return arb(x.numerator) / arb(x.denominator)
    return arb(x)


def enclosure_strings(x, digits=40):
    """Return (lo, hi) decimal strings with lo <= true value <= hi, rigorously.

    Uses arb.mid_rad_10exp, which returns integers (mid, rad, exp) such that x is contained in
    [mid - rad, mid + rad] * 10^exp; the endpoints are then printed exactly.
    """
    mid, rad, e = x.mid_rad_10exp(digits)
    mid, rad, e = int(mid), int(rad), int(e)
    return _dec(mid - rad, e), _dec(mid + rad, e)


def _dec(m, e):
    s = "-" if m < 0 else ""
    m = abs(m)
    if e >= 0:
        return s + str(m) + "0" * e
    digits = str(m).rjust(-e + 1, "0")
    return s + digits[:e] + "." + digits[e:]


def arb_record(x, digits=40):
    """JSON-friendly record of an arb enclosure."""
    lo, hi = enclosure_strings(x, digits)
    return {"enclosure": x.str(digits, radius=True), "lower": lo, "upper": hi,
            "mid_float": float(x.mid()), "radius_float": float(x.rad())}


def gauss_tail_integral_upper(a, R, k):
    """Rigorous upper bound (arb) for int_R^inf r^k exp(-a r^2) dr; a, R arb > 0."""
    a, R = arb_of(a), arb_of(R)
    base = R ** k * (-a * R * R).exp()
    if k <= 0:
        return base / (2 * a * R)
    denom = 2 * a * R - arb(k) / R
    if not denom > 0:
        raise ValueError("gauss_tail_integral_upper: need 2 a R^2 > k")
    return base / denom


def lattice_tail_bound(rho, R, C, j, a):
    """Rigorous upper bound (arb) for sum_{p in P, |p| > R} g(|p|), g(r) = C r^{-j} e^{-a r^2},

    P any set with minimum separation >= 2*rho. Requires g decreasing on [R, inf), i.e.
    2 a R^2 > -j (automatic for j >= 0). See module docstring for the proof.
    """
    rho, R, C, a = arb_of(rho), arb_of(R), arb_of(C), arb_of(a)
    if not (a > 0 and R > 0 and rho > 0):
        raise ValueError("lattice_tail_bound: needs a, R, rho > 0")
    if not (2 * a * R * R + j > 0):
        raise ValueError("lattice_tail_bound: g not decreasing on [R, inf)")
    gR = C * R ** (-j) * (-a * R * R).exp() if j != 0 else C * (-a * R * R).exp()
    first = ((R + rho) / rho) ** 3 * gR
    second = 3 * C / rho ** 3 * (1 + rho / R) ** 2 * gauss_tail_integral_upper(a, R, 2 - j)
    return first + second


def upper_as_arb(x):
    """The exact upper endpoint of x, as an exact arb (rigorous upper bound)."""
    return arb(x.upper())


def interval(lo, hi):
    """arb ball containing [lo, hi] (lo, hi arb)."""
    return arb(lo).union(arb(hi))
