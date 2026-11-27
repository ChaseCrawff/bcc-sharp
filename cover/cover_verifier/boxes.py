"""Exact geometry of boxes: parsing, bisection trees, covering tests, reflection and translation.

A box is a pair (lo, hi) of tuples of eight ``Fraction`` in the order (r1, r2, x, y, z, f1, f2, f3);
it stands for the closed product of the intervals [lo_i, hi_i]  (Section 7.1 of the paper).
Everything in this module is exact rational arithmetic.
"""

from fractions import Fraction
from itertools import product
from math import lcm

# The box K of (4.5).
K_BOX = (
    tuple(map(Fraction, ("5/8", "1/2", "0", "0", "-1/2", "-1/2", "-1/2", "-1/2"))),
    tuple(map(Fraction, ("37/32", "11/8", "1/2", "1/2", "1/2", "1/2", "1/2", "1/2"))),
)


def parse_box(data):
    lo, hi = (tuple(Fraction(v) for v in side) for side in data)
    if len(lo) != 8 or len(hi) != 8 or any(a > b for a, b in zip(lo, hi)):
        raise ValueError("a box needs eight ordered rational intervals")
    return lo, hi


def check_shape_part(box):
    """A box needs r1 > 0 and r2 > 0, so that R(xi) of (4.1) is defined on it.

    Section 7.1 of the paper asks in addition that the shape box lie in the shape part of K.  Some discharged
    boxes of the certificate that are centred on the faces x = 0 or y = 0 of K extend slightly beyond them,
    and such boxes are accepted here.  The only rule that uses the shape part of K is the reduced variant of
    Lemma 7.5(iv) with c_1, which needs x^2 <= 1/4 and tests it (``energy.Support.reduced_shift``).  The boxes
    that the cover has to exhaust are sub-boxes of K by construction.
    """
    if not (box[0][0] > 0 and box[0][1] > 0):
        raise ValueError("the intervals of r1 and r2 must be positive")


def encode(box):
    """Canonical text of a box, used to compare the pieces of consecutive stages exactly."""
    return ",".join(str(v) for side in box for v in side)


def decode(text):
    """Inverse of ``encode``."""
    values = tuple(Fraction(v) for v in text.split(","))
    return values[:8], values[8:]


def bisect(box, axis):
    """The two closed halves of a box cut at the exact midpoint of one coordinate."""
    lo, hi = box
    mid = (lo[axis] + hi[axis]) / 2
    return ((lo, hi[:axis] + (mid,) + hi[axis + 1:]), (lo[:axis] + (mid,) + lo[axis + 1:], hi))


def tree_leaves(box, tree):
    """The leaf boxes of a bisection tree in pre-order.

    ``tree`` is a string: a digit 0..7 bisects that coordinate and is followed by the subtree of the
    lower half and then of the upper half; '.' is a leaf.  The string must be consumed exactly, so a
    tree that parses contains both closed halves of every bisection: its leaves cover the box.
    """
    leaves = []
    stack = [box]
    position = 0
    while stack:
        if position >= len(tree):
            raise ValueError("incomplete bisection tree")
        current = stack.pop()
        symbol = tree[position]
        position += 1
        if symbol == ".":
            leaves.append(current)
        elif symbol in "01234567":
            axis = int(symbol)
            if current[0][axis] == current[1][axis]:
                raise ValueError("bisection of a degenerate interval")
            low, high = bisect(current, axis)
            stack.append(high)
            stack.append(low)
        else:
            raise ValueError("invalid symbol in a bisection tree")
    if position != len(tree):
        raise ValueError("trailing symbols in a bisection tree")
    return leaves


def contains(outer, inner):
    return all(a <= c and d <= b for a, b, c, d in zip(outer[0], outer[1], inner[0], inner[1]))


def meets_in_positive_volume(a, b):
    return all(max(p, r) < min(q, s) for p, q, r, s in zip(a[0], a[1], b[0], b[1]))


def intersection(a, b):
    lo = tuple(max(p, r) for p, r in zip(a[0], b[0]))
    hi = tuple(min(q, s) for q, s in zip(a[1], b[1]))
    return (lo, hi) if all(p <= q for p, q in zip(lo, hi)) else None


def covered(box, parts):
    """True if the closed box is contained in the union of the closed boxes ``parts``.

    Exact recursive test.  If some part contains the box we are done.  Otherwise take a part that
    meets the box in positive volume; one of its faces cuts the box into two closed boxes with
    non-empty interior, and the test is applied to both.  A box of positive volume that meets no
    part in positive volume is not covered (finitely many closed boxes of zero volume inside it
    cannot cover it).  Boxes with a degenerate coordinate are compared in that coordinate by
    containment only.
    """
    dims = [i for i in range(len(box[0])) if box[0][i] < box[1][i]]
    stack = [(box, list(parts))]
    while stack:
        current, candidates = stack.pop()
        candidates = [p for p in candidates
                      if all(p[0][i] <= current[0][i] and current[1][i] <= p[1][i]
                             for i in range(len(current[0])) if i not in dims)
                      and all(max(p[0][i], current[0][i]) < min(p[1][i], current[1][i]) for i in dims)]
        if not candidates:
            return False
        if any(contains(p, current) for p in candidates):
            continue
        part = candidates[0]
        for i in dims:
            cut = None
            if current[0][i] < part[0][i] < current[1][i]:
                cut = part[0][i]
            elif current[0][i] < part[1][i] < current[1][i]:
                cut = part[1][i]
            if cut is not None:
                lo, hi = current
                stack.append(((lo, hi[:i] + (cut,) + hi[i + 1:]), candidates))
                stack.append(((lo[:i] + (cut,) + lo[i + 1:], hi), candidates))
                break
        else:
            raise AssertionError("a part meeting the box without containing it must cut it")
    return True


def reflect(box):
    """The image under iota: (xi, f) -> (xi, -f)  (Section 7.1)."""
    lo, hi = box
    return (lo[:5] + tuple(-v for v in hi[5:]), hi[:5] + tuple(-v for v in lo[5:]))


def translate(box, n):
    """The translate by the integer vector n in the offset  (Lemma 7.2(ii))."""
    if len(n) != 3 or any(type(k) is not int for k in n):
        raise ValueError("an integer translation is required")
    lo, hi = box
    return (lo[:5] + tuple(v + k for v, k in zip(lo[5:], n)), hi[:5] + tuple(v + k for v, k in zip(hi[5:], n)))


def vertices(box):
    """The 256 vertices; vertex number v takes the upper endpoint of coordinate i iff bit 7-i of v is set."""
    return list(product(*zip(*box)))


def shape_vertices(box):
    """The 32 vertices of the shape box (coordinates r1, r2, x, y, z)."""
    return list(product(*zip(box[0][:5], box[1][:5])))


def offset_vertices(box):
    """The 8 vertices of the offset box."""
    return list(product(*zip(box[0][5:], box[1][5:])))


def centre(box):
    return tuple((a + b) / 2 for a, b in zip(*box))


def mirror_step(held):
    """The reflection step of Section 7.8.

    ``held`` is a set of encoded boxes, each on one side of the hyperplane f1 = 0.  Let H+ be those in
    {f1 >= 0} and H- those in {f1 <= 0}.  Returns the set of all boxes P n iota(P') of positive volume
    with P in H+ and P' in H-.

    Why this set may replace ``held`` (it is used once, when no reflection has been used before):
    before the step every point of K lies in a discharged box or in a box of H+ u H-.  Let kappa in K
    with f1 >= 0 lie in no discharged box and in no mirror image of one.  This holds on a neighbourhood U
    of kappa in {f1 >= 0}.  The points kappa' of U with f1 > 0 such that neither kappa' nor iota(kappa')
    lies on a face of a box are dense in U, because there are finitely many faces.  Such a point lies in
    the interior of some P in H+; and iota(kappa'), which has f1 < 0 and lies in no discharged box, lies
    in the interior of some P' in H-.  So kappa' lies in P n iota(P'), which then has positive volume.
    The union of these finitely many closed boxes therefore contains kappa.  For kappa with f1 <= 0 apply
    this to iota(kappa).  Hence after the step every point of K lies in a discharged box, in the mirror
    image of one, in a box of the new set or in the mirror image of one.  This weaker property is
    preserved when a held box is replaced by boxes that cover it, and when no box is held it is the
    statement of Theorem 7.3, because the mirror image of a discharged box is discharged (Lemma 7.2(ii)).
    """
    plus, images = [], []
    for code in held:
        box = decode(code)
        if box[0][5] >= 0:
            plus.append(box)
        elif box[1][5] <= 0:
            images.append(reflect(box))
        else:
            raise ValueError("a held box crosses the hyperplane f1 = 0")
    return {encode(box) for box in positive_intersections(plus, images)}


GRID_COORDINATES = 4        # number of coordinates used for the grid
GRID_LIMIT = 4096           # a box that meets more cells than this is compared with every box of the other list


def positive_intersections(first, second):
    """All boxes a n b of positive volume with a in ``first`` and b in ``second``.

    Exact: every coordinate is multiplied by the common denominator of its endpoints, and a n b has positive
    volume if and only if max(lo_a, lo_b) < min(hi_a, hi_b) in every coordinate, a comparison of integers.
    Candidate pairs are found with a grid in the ``GRID_COORDINATES`` coordinates in which the boxes are
    smallest compared with their range: a box is entered into every cell whose interior meets its interval,
    so that two boxes with a common interior point share a cell.  The grid affects only the running time.
    """
    if not first or not second:
        return []
    dims = len(first[0][0])
    scale = [lcm(*{v.denominator for group in (first, second) for box in group for v in (box[0][c], box[1][c])})
             for c in range(dims)]

    def integers(box):
        return (tuple(v.numerator * (k // v.denominator) for v, k in zip(box[0], scale)),
                tuple(v.numerator * (k // v.denominator) for v, k in zip(box[1], scale)))

    first, second = [integers(box) for box in first], [integers(box) for box in second]
    base = [min(box[0][c] for group in (first, second) for box in group) for c in range(dims)]
    extent = [max(box[1][c] for group in (first, second) for box in group) - base[c] for c in range(dims)]
    size = []
    for c in range(dims):
        widths = sorted(box[1][c] - box[0][c] for box in second)
        size.append(max(1, widths[len(widths) // 2]))                       # the median width
    grid = sorted(range(dims), key=lambda c: -(extent[c] // size[c]))[:GRID_COORDINATES]

    def cells(box):
        """The ranges of cell numbers that the box meets, and their number."""
        ranges, count = [], 1
        for c in grid:
            low = (box[0][c] - base[c]) // size[c]
            high = -((base[c] - box[1][c]) // size[c])                       # ceiling
            ranges.append(range(low, high))
            count *= max(0, high - low)
        return ranges, count

    table, large = {}, []
    for index, box in enumerate(second):
        ranges, count = cells(box)
        if count > GRID_LIMIT:
            large.append(index)
        else:
            for key in product(*ranges):
                table.setdefault(key, []).append(index)
    everything = range(len(second))
    result = []
    for lo, hi in first:
        ranges, count = cells((lo, hi))
        if count > GRID_LIMIT:
            candidates = everything
        else:
            candidates = set(large)
            for key in product(*ranges):
                candidates.update(table.get(key, ()))
        for index in candidates:
            other_lo, other_hi = second[index]
            for c in range(dims):
                if max(lo[c], other_lo[c]) >= min(hi[c], other_hi[c]):
                    break
            else:
                result.append((tuple(Fraction(max(lo[c], other_lo[c]), scale[c]) for c in range(dims)),
                               tuple(Fraction(min(hi[c], other_hi[c]), scale[c]) for c in range(dims))))
    return result
