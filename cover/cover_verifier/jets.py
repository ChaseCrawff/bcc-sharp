"""Second-order Taylor data in ball arithmetic, and the standard lower bounds (5.4)-(5.6) of the paper.

A ``Jet`` holds enclosures of the value, the gradient and the Hessian of a function of n variables,
either at a point (thin balls) or over a box (the variables are balls containing their intervals).
"""

from flint import arb

from .balls import greatest, least, lower, pos_part, sq, upper


class Jet:
    __slots__ = ("v", "g", "h")

    def __init__(self, v, g, h):
        self.v, self.g, self.h = v, g, h

    @staticmethod
    def variable(value, index, n):
        return Jet(value, tuple(arb(int(i == index)) for i in range(n)),
                   tuple(tuple(arb(0) for _ in range(n)) for _ in range(n)))

    @staticmethod
    def constant(value, n):
        value = value if isinstance(value, arb) else arb(value)
        return Jet(value, tuple(arb(0) for _ in range(n)), tuple(tuple(arb(0) for _ in range(n)) for _ in range(n)))

    def _lift(self, other):
        return other if isinstance(other, Jet) else Jet.constant(other, len(self.g))

    def apply(self, f0, f1, f2):
        """Composition phi(u): f0, f1, f2 enclose phi, phi', phi'' at the values of this jet u."""
        n = len(self.g)
        return Jet(f0, tuple(f1 * a for a in self.g),
                   tuple(tuple(f2 * self.g[i] * self.g[j] + f1 * self.h[i][j] for j in range(n)) for i in range(n)))

    def __add__(self, other):
        other = self._lift(other)
        n = len(self.g)
        return Jet(self.v + other.v, tuple(a + b for a, b in zip(self.g, other.g)),
                   tuple(tuple(self.h[i][j] + other.h[i][j] for j in range(n)) for i in range(n)))

    __radd__ = __add__

    def __neg__(self):
        return Jet(-self.v, tuple(-a for a in self.g), tuple(tuple(-a for a in row) for row in self.h))

    def __sub__(self, other):
        return self + (-self._lift(other))

    def __rsub__(self, other):
        return self._lift(other) + (-self)

    def __mul__(self, other):
        if not isinstance(other, Jet):
            other = other if isinstance(other, arb) else arb(other)
            return Jet(self.v * other, tuple(a * other for a in self.g),
                       tuple(tuple(a * other for a in row) for row in self.h))
        n = len(self.g)
        return Jet(self.v * other.v, tuple(self.v * b + other.v * a for a, b in zip(self.g, other.g)),
                   tuple(tuple(self.v * other.h[i][j] + other.v * self.h[i][j]
                               + self.g[i] * other.g[j] + self.g[j] * other.g[i] for j in range(n)) for i in range(n)))

    __rmul__ = __mul__

    def square(self):
        """u^2 with a tight enclosure of the value."""
        n = len(self.g)
        return Jet(sq(self.v), tuple(2 * self.v * a for a in self.g),
                   tuple(tuple(2 * (self.g[i] * self.g[j] + self.v * self.h[i][j]) for j in range(n)) for i in range(n)))

    def inverse(self):
        r = 1 / self.v
        return self.apply(r, -r * r, 2 * r * r * r)

    def __truediv__(self, other):
        return self * (other.inverse() if isinstance(other, Jet) else 1 / (other if isinstance(other, arb) else arb(other)))

    def __rtruediv__(self, other):
        return self.inverse() * other

    def sqrt(self):
        r = self.v.sqrt()
        return self.apply(r, 1 / (2 * r), -1 / (4 * r * self.v))

    def exp(self):
        r = self.v.exp()
        return self.apply(r, r, r)

    def log(self):
        r = 1 / self.v
        return self.apply(self.v.log(), r, -r * r)

    def cos(self):
        s, c = self.v.sin(), self.v.cos()
        return self.apply(c, -s, -c)

    def sin(self):
        s, c = self.v.sin(), self.v.cos()
        return self.apply(s, c, -s)


def variables(values):
    """Jets of the coordinate functions at the given values (balls)."""
    n = len(values)
    return tuple(Jet.variable(v, i, n) for i, v in enumerate(values))


def mean_value_enclosure(centre_value, box_jet, radii):
    """Enclosure over a box of a function with value ``centre_value`` at the centre and gradient enclosed
    by ``box_jet.g`` on the box (mean value theorem, (5.4)), intersected with the direct enclosure
    ``box_jet.v``.  ``radii`` are the half-widths.
    """
    spread = sum((upper(g.abs_upper() * r) for g, r in zip(box_jet.g, radii)), arb(0))
    low = lower(centre_value - spread).max(lower(box_jet.v))
    high = upper(centre_value + spread).min(upper(box_jet.v))
    if not low <= high:
        raise ArithmeticError("inconsistent enclosures")
    return low.union(high)


def floor_first_order(centre_jet, box_jet, radii):
    """(5.4): inf psi >= psi(c) - sum_i rho_i sup |d_i psi|."""
    return lower(centre_jet.v - sum((g.abs_upper() * r for g, r in zip(box_jet.g, radii)), arb(0)))


def one_variable_minimum(g, kappa, rho):
    """min over |v| <= rho of -g |v| + kappa v^2 / 2, for exact g >= 0, kappa, rho > 0  (Lemma C.6(iii))."""
    if kappa > 0 and g <= kappa * rho:
        return lower(-g * g / (2 * kappa))
    return lower(kappa * rho * rho / 2 - g * rho)


def floor_separable(centre_jet, box_jet, radii):
    """(5.5): inf psi >= psi(c) + sum_i min_{|v| <= rho_i} ( -|d_i psi(c)| |v| + kappa_i v^2 / 2 ),
    kappa_i = inf d_ii psi - sum_{j != i} sup |d_ij psi| rho_j / rho_i.  Coordinates with rho_i = 0 are omitted.
    """
    total = centre_jet.v
    n = len(radii)
    for i in range(n):
        if not radii[i] > 0:
            continue
        coupling = sum((box_jet.h[i][j].abs_upper() * radii[j] for j in range(n) if j != i), arb(0))
        kappa = lower(box_jet.h[i][i] - coupling / radii[i])
        total += one_variable_minimum(upper(centre_jet.g[i].abs_upper()), kappa, radii[i])
    return lower(total)


def ldl_pivots(matrix):
    """The pivots of the LDL^T recursion of Lemma C.6(i) on a symmetric matrix of balls, or None if a
    pivot is not certainly positive.  If all pivots are positive, every symmetric matrix with entries in
    the given balls is positive definite.
    """
    n = len(matrix)
    factor = [[arb(0)] * n for _ in range(n)]
    pivots = []
    for j in range(n):
        pivot = matrix[j][j] - sum((sq(factor[j][k]) * pivots[k] for k in range(j)), arb(0))
        if not pivot.is_finite() or not pivot > 0:
            return None
        pivots.append(pivot)
        for i in range(j + 1, n):
            factor[i][j] = (matrix[i][j] - sum((factor[i][k] * factor[j][k] * pivots[k] for k in range(j)), arb(0))) / pivot
    return pivots


def eigenvalue_lower_bound(matrix, steps=40):
    """A lower bound for the least eigenvalue of every symmetric matrix with entries in the given balls.

    As in Section 5.2: with H_0 the matrix of midpoints and rho_ij the radii, if the LDL^T factorization
    of H_0 - t I has positive pivots, the least eigenvalue exceeds t - max_i sum_j rho_ij (Sylvester and
    Weyl).  A suitable t is found by bisection; only successful positivity tests are used.
    """
    n = len(matrix)
    mid = [[matrix[i][j].mid() if i == j else ((matrix[i][j] + matrix[j][i]) / 2).mid() for j in range(n)] for i in range(n)]
    spread = greatest(upper(sum((upper(matrix[i][j].rad() + (matrix[i][j].mid() - mid[i][j]).abs_upper())
                                 for j in range(n)), arb(0))) for i in range(n))

    def positive(t):
        return ldl_pivots([[mid[i][j] - (t if i == j else 0) for j in range(n)] for i in range(n)]) is not None

    low = lower(least(lower(mid[i][i] - sum((mid[i][j].abs_upper() for j in range(n) if j != i), arb(0)))
                      for i in range(n)) - 1)                    # Gershgorin, minus one
    high = upper(least(upper(mid[i][i]) for i in range(n)))
    if not positive(low):
        return None
    for _ in range(steps):
        t = ((low + high) / 2).mid()
        if positive(t):
            low = t
        else:
            high = t
    return lower(low - spread)


def floor_curvature(centre_jet, box_jet, radii):
    """(5.6) in the variables rescaled by the half-widths: with lambda a lower bound for the eigenvalues of
    (rho_i rho_j d_ij psi) over the box and n the number of variables with positive half-width,
        inf psi >= psi(c) - sum_i rho_i |d_i psi(c)| + min(0, lambda) n / 2.
    """
    active = [i for i, r in enumerate(radii) if r > 0]
    base = lower(centre_jet.v - sum((centre_jet.g[i].abs_upper() * radii[i] for i in active), arb(0)))
    if not active:
        return base
    scaled = [[box_jet.h[i][j] * radii[i] * radii[j] for j in active] for i in active]
    if ldl_pivots(scaled) is not None:
        return base
    bound = eigenvalue_lower_bound(scaled)
    if bound is None:
        return None
    return lower(base + bound.min(arb(0)) * len(active) / 2)


def best_floor(centre_jet, box_jet, radii):
    """The largest of the interval value and of the bounds (5.5), (5.6) for inf psi over the box."""
    candidates = [lower(box_jet.v), floor_separable(centre_jet, box_jet, radii), floor_curvature(centre_jet, box_jet, radii)]
    candidates = [c for c in candidates if c is not None and c.is_finite()]
    if not candidates:
        raise ArithmeticError("no finite lower bound")
    return greatest(candidates)


__all__ = ["Jet", "variables", "mean_value_enclosure", "floor_first_order", "floor_separable",
           "floor_curvature", "best_floor", "ldl_pivots", "eigenvalue_lower_bound", "one_variable_minimum",
           "pos_part"]
