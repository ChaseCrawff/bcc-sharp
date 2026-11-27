"""Crystal structures in exact rational "natural units".

A structure is a Bravais lattice Lambda = B Z^3 (columns of B = primitive vectors) with a
basis of n points s_j = B f_j (fractional coordinates f_j) carrying charges q_j.

Everything the Ewald code needs is exact rational in natural units:
  * the Gram (metric) matrix M = B^T B,   |B v|^2 = v^T M v,
  * the fractional coordinates f_j,
  * |G|^2 = 4 pi^2 h^T M^{-1} h for G = 2 pi B^{-T} h in the reciprocal lattice,
  * G . s_j = 2 pi h . f_j.
For sc/bcc/fcc (cube side 1) and for hcp with rational (c/a)^2 the Gram matrix is rational.

Physical (Wigner-Seitz) units: lengths are rescaled by s = (4 pi n / (3 V))^{1/3}, V = sqrt(det M),
so that the volume per particle is 4 pi / 3 (Wigner-Seitz radius a = 1). Coulomb energies
then scale as E_WS = E_nat / s, i.e. E_WS is in units of e^2/a.
"""

from dataclasses import dataclass
from fractions import Fraction as Fr

from .exact import mat, matmul, transpose, det3, F


@dataclass(frozen=True)
class Structure:
    name: str
    gram: tuple          # M = B^T B, 3x3 Fractions
    frac: tuple          # n fractional coordinates (3-tuples of Fractions)
    charges: tuple       # n integer charges
    cart: tuple = None   # optional exact Cartesian B (3x3 Fractions, columns = primitive vectors)
    note: str = ""

    @property
    def n(self):
        return len(self.frac)

    @property
    def total_charge(self):
        return sum(self.charges)

    @property
    def det_gram(self):
        return det3(self.gram)

    def describe(self):
        return {
            "name": self.name,
            "gram_matrix_natural_units": [[str(x) for x in r] for r in self.gram],
            "fractional_basis": [[str(x) for x in f] for f in self.frac],
            "charges": list(self.charges),
            "cartesian_primitive_vectors_columns": (None if self.cart is None
                                                    else [[str(x) for x in r] for r in self.cart]),
            "note": self.note,
        }


def _from_cart(name, B_rows, frac, charges, note=""):
    """B_rows: 3x3 rows of the matrix B whose COLUMNS are the primitive vectors."""
    B = mat(B_rows)
    M = matmul(transpose(B), B)
    frac = tuple(tuple(F(x) for x in f) for f in frac)
    return Structure(name, M, frac, tuple(charges), B, note)


def _cols(*vectors):
    """Build B (rows) from primitive vectors given as columns."""
    return [[vectors[j][i] for j in range(3)] for i in range(3)]


h = Fr(1, 2)


def sc():
    return _from_cart("sc", _cols((1, 0, 0), (0, 1, 0), (0, 0, 1)), [(0, 0, 0)], [1],
                      "simple cubic, cube side 1")


def bcc_primitive():
    return _from_cart("bcc", _cols((-h, h, h), (h, -h, h), (h, h, -h)), [(0, 0, 0)], [1],
                      "bcc, primitive cell, conventional cube side 1")


def bcc_conventional():
    return _from_cart("bcc_conv", _cols((1, 0, 0), (0, 1, 0), (0, 0, 1)),
                      [(0, 0, 0), (h, h, h)], [1, 1], "bcc, conventional cube (2 points), side 1")


def fcc_primitive():
    return _from_cart("fcc", _cols((0, h, h), (h, 0, h), (h, h, 0)), [(0, 0, 0)], [1],
                      "fcc, primitive cell, conventional cube side 1")


def fcc_conventional():
    return _from_cart("fcc_conv", _cols((1, 0, 0), (0, 1, 0), (0, 0, 1)),
                      [(0, 0, 0), (0, h, h), (h, 0, h), (h, h, 0)], [1, 1, 1, 1],
                      "fcc, conventional cube (4 points), side 1")


def hcp(gamma2=Fr(8, 3)):
    """hcp with a = 1 and (c/a)^2 = gamma2 (exact rational). Ideal: gamma2 = 8/3.

    Hexagonal primitive vectors a1 = (1,0,0), a2 = (-1/2, sqrt3/2, 0), a3 = (0,0,c): Gram matrix
    [[1,-1/2,0],[-1/2,1,0],[0,0,gamma2]] (rational although a2 has an irrational coordinate).
    Basis at fractional (0,0,0) and (1/3,2/3,1/2).
    """
    gamma2 = F(gamma2)
    M = mat([[1, -h, 0], [-h, 1, 0], [0, 0, gamma2]])
    frac = ((Fr(0), Fr(0), Fr(0)), (Fr(1, 3), Fr(2, 3), Fr(1, 2)))
    name = "hcp" if gamma2 == Fr(8, 3) else f"hcp_gamma2={gamma2}"
    return Structure(name, M, frac, (1, 1), None, f"hcp, a=1, (c/a)^2={gamma2}")


def nacl():
    """Rock salt with nearest-neighbour distance 1 (fcc with cube side 2). Test structure."""
    return _from_cart("NaCl", _cols((0, 1, 1), (1, 0, 1), (1, 1, 0)),
                      [(0, 0, 0), (-h, h, h)], [1, -1], "rock salt, nearest-neighbour distance 1")


def cscl():
    """Caesium chloride, cube side 1 (nearest-neighbour distance sqrt(3)/2). Test structure."""
    return _from_cart("CsCl", _cols((1, 0, 0), (0, 1, 0), (0, 0, 1)),
                      [(0, 0, 0), (h, h, h)], [1, -1], "CsCl, cube side 1")


def periodic_configuration(name, L, points, charges=None, note=""):
    """A configuration of points on the cubic torus R^3 / (L Z^3).

    points: Cartesian coordinates (Fractions) of the particles in one period cell.
    Returned as a Structure with B = L*I (so the fractional coordinates are points/L mod 1).
    """
    L = F(L)
    frac = tuple(tuple((F(x) / L) % 1 for x in p) for p in points)
    if len(set(frac)) != len(frac):
        raise ValueError("coincident charges modulo the period lattice")
    if charges is None:
        charges = [1] * len(frac)
    B = _cols((L, 0, 0), (0, L, 0), (0, 0, L))
    return _from_cart(name, B, frac, charges, note)


OCP_STRUCTURES = {
    "bcc": bcc_primitive,
    "fcc": fcc_primitive,
    "hcp": hcp,
    "sc": sc,
}
