"""The defect on a box (Section 7.5): registrations, the bounds of Lemma 7.8, the separately convex
majorant used in Lemma 7.9(ii), the complete list of Lemma 7.8(iv) and the growth coefficient of
Lemma C.5.

A registration is a triple (B', f0, n): B' a basis matrix with det B' = 1 of a sublattice of index two
of B_0 = Z^3 u (Z^3 + (1/2,1/2,1/2)), f0 in (1/2)Z^3 \\ Z^3 with B' f0 in B_0 \\ B' Z^3, and n in Z^3.
With A = R(xi) B'^-1, C = A^T A, delta = f - f0 - n, h = R(xi) delta  (7.9):
    d_0 = 100 |C^(1/2) - I|_F^2,     q = d_0 + 200 |h|^2.
"""

from fractions import Fraction
from itertools import product
from math import ceil, floor, isqrt

from flint import arb

from . import shape
from .balls import ball, greatest, hull, least, lower, pos_part, sq, upper
from .boxes import centre, offset_vertices, shape_vertices

# The twelve vectors of B_0 of length sqrt 2.
TWELVE = tuple(b for b in product((-1, 0, 1), repeat=3) if sum(x * x for x in b) == 2)
HALF = Fraction(1, 2)


def d_sharp_lower():
    """A lower bound for d_sharp = (600/11) (sqrt 2 - 13/10)^2 of Lemma 7.8(ii)."""
    return lower(ball(Fraction(600, 11)) * (arb(2).sqrt() - ball(Fraction(13, 10))) ** 2)


# ---------------------------------------------------------------------------------------------
# Exact linear algebra for registrations
# ---------------------------------------------------------------------------------------------
def det3(a):
    return (a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1])
            - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0])
            + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0]))


def inverse3(a):
    d = det3(a)
    if d == 0:
        raise ValueError("singular matrix")
    cof = [[a[(i + 1) % 3][(j + 1) % 3] * a[(i + 2) % 3][(j + 2) % 3]
            - a[(i + 1) % 3][(j + 2) % 3] * a[(i + 2) % 3][(j + 1) % 3] for j in range(3)] for i in range(3)]
    return tuple(tuple(Fraction(cof[j][i], 1) / d for j in range(3)) for i in range(3))


def matvec(a, v):
    return tuple(sum(a[i][j] * v[j] for j in range(3)) for i in range(3))


def in_b0(v):
    """v in B_0: all coordinates integers or all coordinates half-odd integers."""
    return all(x.denominator == 1 for x in v) or all(x.denominator == 2 for x in v)


class Registration:
    """A checked registration (B', f0, n) with W = B'^-1 and the labels chi(b) of the twelve vectors."""

    def __init__(self, basis, f0, n):
        self.basis = tuple(tuple(Fraction(v) for v in row) for row in basis)
        self.f0 = shape.half_offset(f0)
        self.n = tuple(n)
        if len(self.basis) != 3 or any(len(row) != 3 for row in self.basis):
            raise ValueError("B' must be a 3x3 matrix")
        columns = tuple(zip(*self.basis))
        if det3(self.basis) != 1 or not all(in_b0(c) for c in columns):
            raise ValueError("B' is not a basis of determinant one of a sublattice of B_0")
        if not in_b0(matvec(self.basis, self.f0)):
            raise ValueError("f0 is not the half class of B'")
        if len(self.n) != 3 or any(type(k) is not int for k in self.n):
            raise ValueError("n must be an integer vector")
        self.w = inverse3(self.basis)
        # chi(b) = 0 if b in B' Z^3 and 1 otherwise; in the second case B'^-1 b is in Z^3 + f0.
        self.labels = []
        for b in TWELVE:
            coordinates = matvec(self.w, b)
            odd = any(c.denominator != 1 for c in coordinates)
            if odd and any((c - f).denominator != 1 for c, f in zip(coordinates, self.f0)):
                raise ArithmeticError("a vector of B_0 outside both cosets")
            self.labels.append((b, coordinates, int(odd)))

    def delta(self, box):
        """Exact endpoints of delta = f - f0 - n on the offset box."""
        lo = tuple(a - f - k for a, f, k in zip(box[0][5:], self.f0, self.n))
        hi = tuple(b - f - k for b, f, k in zip(box[1][5:], self.f0, self.n))
        return lo, hi


def deformation(xi, w):
    """A = R(xi) W, rows first: A_1 = r1 (w_1 + x w_2 + y w_3), A_2 = r2 (w_2 + z w_3), A_3 = w_3/(r1 r2)."""
    r1, r2, x, y, z = xi
    return (tuple(r1 * (w[0][j] + x * w[1][j] + y * w[2][j]) for j in range(3)),
            tuple(r2 * (w[1][j] + z * w[2][j]) for j in range(3)),
            tuple(w[2][j] / (r1 * r2) for j in range(3)))


def strain_data(xi, w):
    """Enclosures over a shape box of C - I (nine entries), |C - I|_F^2 and the row-sum bound r_C."""
    a = deformation(xi, tuple(tuple(map(ball, row)) for row in w))
    c = [[None] * 3 for _ in range(3)]
    for i in range(3):
        for j in range(i, 3):
            if i == j:
                c[i][j] = sum((sq(a[k][i]) for k in range(3)), arb(0)) - 1
            else:
                c[i][j] = c[j][i] = sum((a[k][i] * a[k][j] for k in range(3)), arb(0))
    norm2 = sum((sq(c[i][j]) for i in range(3) for j in range(3)), arb(0))
    radius = greatest(upper(sum((upper(abs_ball(c[i][j])) for j in range(3)), arb(0))) for i in range(3))
    return c, norm2, radius


def abs_ball(x):
    """An exact upper bound for |x| on the ball x, as a ball."""
    return x.abs_upper()


def d0_bounds(xi, w):
    """(d^-, d^+) with d^- <= d_0 <= d^+ on the shape box xi (Section C.2); d^+ is None if r_C >= 1.

    The eigenvalues c of C lie in [1 - r_C, 1 + r_C] and (sqrt c - 1)^2 = (c - 1)^2 / (1 + sqrt c)^2.
    """
    _, norm2, radius = strain_data(xi, w)
    low = pos_part(lower(100 * lower(norm2) / (1 + (1 + radius).sqrt()) ** 2))
    high = upper(100 * upper(norm2) / (1 + (1 - radius).sqrt()) ** 2) if radius < 1 else None
    return lower(low), high


def shape_ball(box):
    """The five shape coordinates of a box as balls containing their intervals."""
    return tuple(hull(a, b) for a, b in zip(box[0][:5], box[1][:5]))


def squared_norm(v):
    return sum((sq(x) for x in v), arb(0))


def phi_upper(squared_length):
    """An upper bound for the weight phi(|y|) of a possible neighbour, from an enclosure of |y|^2  (3.2)."""
    length = lower(pos_part(lower(squared_length)).sqrt())
    return pos_part(upper(13 - 10 * length)).min(arb(1))


def defect_upper(box, registration):
    """D_+ >= D on the box, from one registration, or None if the bound is not below one.

    Lemma 7.8(ii): if q < 1 then D = min{1, q + Phi}, Phi the sum of phi(|R v|) over the twelve vectors
    b of length sqrt 2, v = B'^-1 b + chi(b) delta, and Phi = 0 if q <= d_sharp.  With d_0 <= d^+
    (Section C.2) this gives D <= d^+ + 200 sup |h|^2 + sum of sup phi, provided the right side is < 1.
    """
    xi = shape_ball(box)
    _, d_plus = d0_bounds(xi, registration.w)
    if d_plus is None:
        return None
    d_lo, d_hi = registration.delta(box)
    delta = tuple(hull(a, b) for a, b in zip(d_lo, d_hi))
    bound = upper(d_plus + 200 * upper(squared_norm(shape.real_vector(xi, delta))))
    if not bound <= d_sharp_lower():
        for _, coordinates, odd in registration.labels:
            v = tuple(ball(c) + odd * t for c, t in zip(coordinates, delta))
            bound += phi_upper(squared_norm(shape.real_vector(xi, v)))
        bound = upper(bound)
    return bound if bound < 1 else None


# ---------------------------------------------------------------------------------------------
# The separately convex majorant of the trial cost (text after Lemma 7.9)
# ---------------------------------------------------------------------------------------------
def rotation_from_quaternion(quaternion):
    """The rational rotation matrix of a nonzero integer quaternion (x, y, z, w); checked to lie in SO(3)."""
    if len(quaternion) != 4 or any(type(v) is not int for v in quaternion):
        raise ValueError("four integers required")
    x, y, z, w = quaternion
    norm = x * x + y * y + z * z + w * w
    if norm == 0:
        raise ValueError("zero quaternion")
    u = tuple(tuple(Fraction(t, norm) for t in row) for row in (
        (norm - 2 * (y * y + z * z), 2 * (x * y - z * w), 2 * (x * z + y * w)),
        (2 * (x * y + z * w), norm - 2 * (x * x + z * z), 2 * (y * z - x * w)),
        (2 * (x * z - y * w), 2 * (y * z + x * w), norm - 2 * (x * x + y * y))))
    identity = all(sum(u[k][i] * u[k][j] for k in range(3)) == (i == j) for i in range(3) for j in range(3))
    if not identity or det3(u) != 1:
        raise ArithmeticError("the matrix of a quaternion must be a rotation")
    return u


def cost_vertices(box, registration, rotation):
    """Balls C(v) at the 256 vertices of the box for the majorant

        C = 100 |A - U|_F^2 + 200 |h|^2 + sum (13 - 10 L)_+        (text after Lemma 7.9),

    which is separately convex and satisfies C >= 100 |A - U|_F^2 + 200 |h|^2 + Phi >= D on the box
    (Lemma 7.8(iii)).  Returns None if the convexity condition 9 |w|^2 >= 4 (r1^+ r2^+)^2 fails
    (w the third row of B'^-1; exact arithmetic).
    """
    lo, hi = box
    w = registration.w
    if 9 * sum(v * v for v in w[2]) < 4 * (hi[0] * hi[1]) ** 2:
        return None
    w_ball = tuple(tuple(map(ball, row)) for row in w)
    u_ball = tuple(tuple(map(ball, row)) for row in rotation)
    d_lo, d_hi = registration.delta(box)
    deltas = [tuple(map(ball, d)) for d in product(*zip(d_lo, d_hi))]
    shapes = [tuple(map(ball, s)) for s in shape_vertices(box)]
    table = []
    for xi in shapes:
        a = deformation(xi, w_ball)
        strain = 100 * sum((sq(a[i][j] - u_ball[i][j]) for i in range(3) for j in range(3)), arb(0))
        for delta in deltas:
            table.append(strain + 200 * squared_norm(shape.real_vector(xi, delta)))
    if not all(v.is_finite() for v in table):
        raise ArithmeticError("non-finite strain or displacement")
    if greatest(upper(v) for v in table) <= d_sharp_lower():
        return table            # q <= d_sharp on the box, so Phi = 0 (Lemma 7.8(ii))
    xi_box = shape_ball(box)
    delta_box = tuple(hull(a, b) for a, b in zip(d_lo, d_hi))
    xi_mid = tuple(map(ball, centre(box)[:5]))
    delta_mid = tuple(ball((a + b) / 2) for a, b in zip(d_lo, d_hi))
    r1m, r2m, r1p, r2p = (ball(v) for v in (lo[0], lo[1], hi[0], hi[1]))
    # Delta >= sigma_1(r1) sigma_2(r2) - 1/(r1 r2) >= 0 for the chords sigma_i of 1/t
    chord_error = upper(sq(r1p - r1m) / (4 * r1m * r1m * r1p * r2m) + sq(r2p - r2m) / (4 * r2m * r2m * r2p * r1m))
    for _, coordinates, odd in registration.labels:
        v_box = tuple(ball(c) + odd * t for c, t in zip(coordinates, delta_box))
        if lower(squared_norm(shape.real_vector(xi_box, v_box))) >= ball(Fraction(169, 100)):
            continue            # |R v| >= 13/10 on the whole box: never a neighbour
        middle = shape.real_vector(xi_mid, tuple(ball(c) + odd * t for c, t in zip(coordinates, delta_mid)))
        norm = squared_norm(middle).sqrt()
        if not norm > 0:
            raise ArithmeticError("vanishing central vector")
        p = tuple(x / norm for x in middle)          # encloses a unit vector
        loss = chord_error * upper(abs_ball(p[2] * v_box[2]))
        for i, xi in enumerate(shapes):
            for j, delta in enumerate(deltas):
                y = shape.real_vector(xi, tuple(ball(c) + odd * t for c, t in zip(coordinates, delta)))
                table[8 * i + j] += pos_part(13 - 10 * (shape.dot(p, y) - loss))
    return table


# ---------------------------------------------------------------------------------------------
# The complete list of Lemma 7.8(iv)
# ---------------------------------------------------------------------------------------------
def _square_range(a, b):
    """Exact range of t^2 for t in [a, b]."""
    return (Fraction(0) if a <= 0 <= b else min(a * a, b * b), max(a * a, b * b))


def _length_range(lo, hi, m):
    """Exact numbers a <= |R(xi) m|^2 <= b for all xi in the shape box [lo, hi]."""
    r1, r2, x, y, z = lo
    r1p, r2p, xp, yp, zp = hi
    first = _square_range(m[0] + min(x * m[1], xp * m[1]) + min(y * m[2], yp * m[2]),
                          m[0] + max(x * m[1], xp * m[1]) + max(y * m[2], yp * m[2]))
    second = _square_range(m[1] + min(z * m[2], zp * m[2]), m[1] + max(z * m[2], zp * m[2]))
    third = Fraction(m[2] * m[2])
    return (r1 * r1 * first[0] + r2 * r2 * second[0] + third / (r1p * r2p) ** 2,
            r1p * r1p * first[1] + r2p * r2p * second[1] + third / (r1 * r2) ** 2)


_LIST_CACHE = {}


def registration_list(lo, hi):
    """All pairs (B', f0), up to rotations preserving B_0, with d_0 < 1 somewhere in the shape box.

    Lemma 7.8(iv): d_0 < 1 gives |C^(1/2) - I|_F < 1/10, hence (9/10)|B'm| <= |R(xi)m| <= (11/10)|B'm|
    for all m in Z^3.  For m = e_i and m = e_i +- e_j this confines |B'e_i|^2 and |B'e_i +- B'e_j|^2 to
    [(100/121) inf |R m|^2, (100/81) sup |R m|^2]; the vectors of B_0 in these ranges are enumerated in
    exact arithmetic.  Two bases with the same Gram matrix B'^T B' and the same half class differ by a
    rotation preserving B_0, and one of them is kept.  The list may contain pairs with d_0 >= 1.
    """
    key = (tuple(lo), tuple(hi))
    if key in _LIST_CACHE:
        return _LIST_CACHE[key]
    axes = ((1, 0, 0), (0, 1, 0), (0, 0, 1))

    def band(m):                      # range of |2 B' m|^2, an integer
        a, b = _length_range(lo, hi, m)
        return ceil(Fraction(400, 121) * a), floor(Fraction(400, 81) * b)

    bands = [band(m) for m in axes]
    side = isqrt(max(b for _, b in bands))
    doubled = [p for p in product(range(-side, side + 1), repeat=3) if p[0] % 2 == p[1] % 2 == p[2] % 2]
    norms = {p: sum(v * v for v in p) for p in doubled}
    columns = [[p for p in doubled if a <= norms[p] <= b and norms[p] > 0] for a, b in bands]
    pair_bands = {(i, j, s): band(tuple(axes[i][k] + s * axes[j][k] for k in range(3)))
                  for i in range(3) for j in range(i + 1, 3) for s in (-1, 1)}

    def pair_ok(p, q, i, j):
        total, cross = norms[p] + norms[q], 2 * sum(a * b for a, b in zip(p, q))
        return all(pair_bands[i, j, s][0] <= total + s * cross <= pair_bands[i, j, s][1] for s in (-1, 1))

    found = {}
    for p0 in columns[0]:
        for p1 in columns[1]:
            if not pair_ok(p0, p1, 0, 1):
                continue
            for p2 in columns[2]:
                if not pair_ok(p0, p2, 0, 2) or not pair_ok(p1, p2, 1, 2):
                    continue
                basis = tuple(tuple(Fraction(c[i], 2) for c in (p0, p1, p2)) for i in range(3))
                if det3(basis) != 1:
                    continue
                halves = [f for f in product((Fraction(0), HALF), repeat=3)
                          if any(f) and in_b0(matvec(basis, f))]
                if len(halves) != 1:
                    raise ArithmeticError("a sublattice of index two has exactly one half class")
                cols = (p0, p1, p2)
                gram_key = tuple(sum(a * b for a, b in zip(cols[i], cols[j])) for i in range(3) for j in range(i + 1))
                found.setdefault((gram_key, halves[0]), (basis, halves[0]))
    result = tuple(found[k] for k in sorted(found))
    if len(_LIST_CACHE) > 4096:
        _LIST_CACHE.clear()
    _LIST_CACHE[key] = result
    return result


def same_class(f, g):
    """f = g modulo Z^3."""
    return all((Fraction(a) - Fraction(b)).denominator == 1 for a, b in zip(f, g))


# ---------------------------------------------------------------------------------------------
# The coefficient of the growth of the defect (Lemma C.5)
# ---------------------------------------------------------------------------------------------
def rho(v, c):
    """An upper bound for sup_{0 < s <= v} 10 (s - c)_+ / s^2   (C.6)."""
    if v <= c:
        return arb(0)
    if v < 2 * c:
        return upper(10 * (v - c) / v ** 2)
    return upper(ball(Fraction(5, 2)) / c)


class AnchorDefect:
    """Data of Lemma C.5 on a shape box S for anchors with half class f0: for every pair (B', f0) of the
    complete list with d^- < 1, the bounds d^-, d^+ and, for each pair +-b of vectors of B_0 of length
    sqrt 2 with chi(b) = 1, the vector B'^-1 b, a lower bound q_b^- for |A b|^2 and
    c_b = max{(23/25) sqrt 2, sqrt(q_b^-)} - 13/10.
    """

    def __init__(self, lo, hi, f0, list_box=None):
        self.xi = tuple(hull(a, b) for a, b in zip(lo, hi))
        self.gram = shape.gram(self.xi)
        candidates = registration_list(*(list_box if list_box is not None else (tuple(lo), tuple(hi))))
        clearance = lower(ball(Fraction(23, 25)) * arb(2).sqrt() - ball(Fraction(13, 10)))
        self.entries = []
        self.frames = []                    # B'^-1 for all pairs of the list with half class f0
        self.centre = tuple((Fraction(a) + Fraction(b)) / 2 for a, b in zip(lo, hi))
        for basis, half in candidates:
            if not same_class(half, f0):
                continue
            w = inverse3(basis)
            self.frames.append(w)
            d_minus, d_plus = d0_bounds(self.xi, w)
            if d_minus >= 1:
                continue
            pairs = []
            for b in TWELVE:
                if not b > (0, 0, 0):
                    continue
                coordinates = matvec(w, b)
                if all(c.denominator == 1 for c in coordinates):
                    continue                                   # chi(b) = 0
                u = tuple(map(ball, coordinates))
                q_minus = pos_part(lower(squared_norm(shape.real_vector(self.xi, u))))
                c_b = clearance.max(lower(q_minus.sqrt() - ball(Fraction(13, 10))))
                pairs.append((u, q_minus, c_b))
            self.entries.append((d_minus, d_plus, pairs))
        # D(xi, f0) >= D_0^- on S (last statement of Lemma C.5)
        self.d0_minus = least([arb(1)] + [e[0] for e in self.entries])

    def closest_frame(self):
        """B'^-1 for the pair of the list with half class f0 that has the least |C - I|_F at the centre of
        S (exact arithmetic), or None if the list has no such pair  (text after Lemma C.12)."""
        def score(w):
            a = deformation(self.centre, w)
            c = [[sum(a[k][i] * a[k][j] for k in range(3)) - (i == j) for j in range(3)] for i in range(3)]
            return sum(v * v for row in c for v in row)
        return min(self.frames, key=score) if self.frames else None

    def gamma(self, delta, h2_lower, h2_upper):
        """gamma >= max over the list of min{gamma_cap, gamma_ann}: then D(xi,f) - D(xi,f0) <= gamma |h|^2
        for xi in S and delta = f - f0 - n in the box ``delta`` (balls), where h2_lower <= |h|^2 <= h2_upper.
        """
        best = arb(0)
        h_plus = upper(h2_upper.sqrt())
        image = shape.sym_apply(self.gram, delta)             # M delta
        cut = d_sharp_lower()
        for d_minus, d_plus, pairs in self.entries:
            cap = upper(1 - d_minus)
            gamma_cap = upper(cap / h2_lower) if h2_lower > 0 else None                    # (a)
            if d_plus is not None and upper(d_plus + 200 * h2_upper) <= cut:               # (b)
                gamma_ann = arb(200)
            else:                                                                          # (c)
                h_star = h_plus.min(upper((cap / 200).sqrt()))
                gamma_ann = arb(200)
                for u, q_minus, c_b in pairs:
                    term = rho(h_star, c_b)
                    if h2_lower > 0:
                        p_b = upper(abs_ball(shape.dot(u, image)))                          # |A b . h|
                        other = upper(pos_part(4 * (ball(Fraction(169, 100)) - q_minus + 2 * p_b - h2_lower))
                                      / h2_lower)
                        term = term.min(other)
                    gamma_ann += term
                gamma_ann = upper(gamma_ann)
            value = gamma_ann if gamma_cap is None else gamma_ann.min(gamma_cap)
            best = best.max(upper(value))
        return upper(best)
