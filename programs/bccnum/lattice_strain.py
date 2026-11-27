r"""Strain chart at a cubic minimum (bcc or fcc) for the certificate of the lattice case (Proposition 5.2).

Chart. B0 is a basis of the covolume-one lattice L0 (bcc or fcc) in its cubic frame (Muratov and Novaga [29], (10)). For w in R^5,
    S(w) = sum_k sigma_k w_k E_k            (E_k: orthonormal basis of traceless symmetric 3x3 matrices, cubic irreps:
                                              E_1 = diag(1,-1,0)/sqrt2, E_2 = diag(1,1,-2)/sqrt6         (E_g),
                                              E_3, E_4, E_5 = (e_i e_j^T + e_j e_i^T)/sqrt2, ij = 12, 13, 23 (T_2g)),
    d(w) = det(I + S) = 1 - tr(S^2)/2 + det S,
    C(w) = d^{-1/3} (I + S)                 (det C = 1),
    Y(w) = B0^T C(w) B0                      (Gram matrix of the covolume-one lattice C^{1/2} L0).
By Cayley-Hamilton (tr S = 0): adj(I + S) = (1 - tr(S^2)/2) I - S + S^2, so (I + S)^{-1} = adj/d, C^{-1} = d^{-2/3} adj, and for m in Z^3,
    Y[m]      = d^{-1/3} (|a|^2 + a^T S a),                         a = B0 m,
    Y^{-1}[m] = d^{-2/3} (|v|^2 (1 - tr(S^2)/2) - v^T S v + |S v|^2),  v = B0^{-T} m.
The sigma_k are fixed positive floats (whitening; any positive values are admissible).
"""

import math

from flint import arb

from bccnum.lattice_cert import NV, Jet, G_values, term_jet, half_set, _family_tail


def irreps():
    s2 = arb(2).sqrt()
    s6 = arb(6).sqrt()
    Z = arb(0)
    E = [[[1 / s2, Z, Z], [Z, -1 / s2, Z], [Z, Z, Z]],
         [[1 / s6, Z, Z], [Z, 1 / s6, Z], [Z, Z, -2 / s6]]]
    for (i, j) in ((0, 1), (0, 2), (1, 2)):
        M = [[Z, Z, Z] for _ in range(3)]
        M[i][j] = 1 / s2
        M[j][i] = 1 / s2
        E.append(M)
    return E


class Chart:
    def __init__(self, B0, sigma):
        """B0: 3x3 balls (columns = basis vectors, cubic frame, covolume one). sigma: 5 positive floats."""
        self.B0 = B0
        self.sigma = [arb(s) for s in sigma]
        self.E = irreps()
        # B0^{-T}
        a, b, c = B0[0]
        d, e, f = B0[1]
        g, h, i = B0[2]
        det = a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)
        inv = [[(e * i - f * h) / det, (c * h - b * i) / det, (b * f - c * e) / det],
               [(f * g - d * i) / det, (a * i - c * g) / det, (c * d - a * f) / det],
               [(d * h - e * g) / det, (b * g - a * h) / det, (a * e - b * d) / det]]
        self.B0inv = inv
        self.B0invT = [[inv[j][i] for j in range(3)] for i in range(3)]
        self._cache = {}

    def vectors(self, m):
        if m not in self._cache:
            a = [sum((self.B0[i][k] * m[k] for k in range(3)), arb(0)) for i in range(3)]
            v = [sum((self.B0invT[i][k] * m[k] for k in range(3)), arb(0)) for i in range(3)]
            na = sum((x * x for x in a), arb(0))
            nv = sum((x * x for x in v), arb(0))
            aEa = [sum((a[i] * Ek[i][j] * a[j] for i in range(3) for j in range(3)), arb(0)) for Ek in self.E]
            vEv = [sum((v[i] * Ek[i][j] * v[j] for i in range(3) for j in range(3)), arb(0)) for Ek in self.E]
            self._cache[m] = (a, v, na, nv, aEa, vEv)
        return self._cache[m]

    def S_jets(self, wb):
        """S (3x3 jets), linear in w."""
        S = [[Jet.const(0) for _ in range(3)] for _ in range(3)]
        for k in range(NV):
            wk = Jet.var(wb[k], k) * self.sigma[k]
            for i in range(3):
                for j in range(3):
                    e = self.E[k][i][j]
                    if not e.is_zero():
                        S[i][j] = S[i][j] + wk * e
        return S

    def base(self, wb):
        S = self.S_jets(wb)
        trS2 = Jet.const(0)
        for k in range(NV):
            wk = Jet.var(wb[k], k) * self.sigma[k]
            trS2 = trS2 + wk.sq()
        detS = (S[0][0] * (S[1][1] * S[2][2] - S[1][2] * S[2][1]) - S[0][1] * (S[1][0] * S[2][2] - S[1][2] * S[2][0])
                + S[0][2] * (S[1][0] * S[2][1] - S[1][1] * S[2][0]))
        d = trS2 * (-arb(1) / 2) + detS + 1
        third = arb(1) / 3
        dv = d.v
        dm13 = d.apply(dv ** (-third), -third * dv ** (-third - 1), third * (third + 1) * dv ** (-third - 2))
        dm23 = d.apply(dv ** (-2 * third), -2 * third * dv ** (-2 * third - 1),
                       2 * third * (2 * third + 1) * dv ** (-2 * third - 2))
        return S, trS2, d, dm13, dm23

    def H_partial(self, wb, mset, base=None):
        """Jet (in w) of P = 2 sum_{m in mset} [G(1/2, pi Y[m]) + G(1, pi Y^{-1}[m])]."""
        S, trS2, d, dm13, dm23 = base if base is not None else self.base(wb)
        wj = [Jet.var(wb[k], k) * self.sigma[k] for k in range(NV)]
        half = arb(1) / 2
        one_m = trS2 * (-half) + 1
        total = Jet.const(0)
        for m in mset:
            a, v, na, nv, aEa, vEv = self.vectors(m)
            lin = Jet.const(na)
            vSv = Jet.const(0)
            for k in range(NV):
                lin = lin + wj[k] * aEa[k]
                vSv = vSv + wj[k] * vEv[k]
            Sv = [sum((S[i][j] * v[j] for j in range(3)), Jet.const(0)) for i in range(3)]
            q = one_m * nv - vSv + Sv[0].sq() + Sv[1].sq() + Sv[2].sq()
            Q = dm13 * lin
            Qs = dm23 * q
            total = total + term_jet(Q, half) + term_jet(Qs, 1)
        return total * 2

    def C_jets(self, wb, base=None):
        S, trS2, d, dm13, dm23 = base if base is not None else self.base(wb)
        return [[dm13 * (S[i][j] + (1 if i == j else 0)) for j in range(3)] for i in range(3)]

    def Q_defect(self, wb, kappa, base=None):
        C = self.C_jets(wb, base)
        tot = Jet.const(0)
        for i in range(3):
            for j in range(3):
                tot = tot + (C[i][j] - (1 if i == j else 0)).sq()
        return tot * kappa, C

    def Y_Yi_jets(self, wb, base=None):
        S, trS2, d, dm13, dm23 = base if base is not None else self.base(wb)
        C = [[dm13 * (S[i][j] + (1 if i == j else 0)) for j in range(3)] for i in range(3)]
        S2 = [[sum((S[i][k] * S[k][j] for k in range(3)), Jet.const(0)) for j in range(3)] for i in range(3)]
        one_m = trS2 * (-arb(1) / 2) + 1
        adj = [[S2[i][j] - S[i][j] + (one_m if i == j else 0) for j in range(3)] for i in range(3)]
        Ci = [[dm23 * adj[i][j] for j in range(3)] for i in range(3)]
        B0, Bi = self.B0, self.B0inv
        Y = [[sum((C[k][l] * (B0[k][i] * B0[l][j]) for k in range(3) for l in range(3)), Jet.const(0)) for j in range(3)]
             for i in range(3)]
        Yi = [[sum((Ci[k][l] * (Bi[i][k] * Bi[j][l]) for k in range(3) for l in range(3)), Jet.const(0)) for j in range(3)]
              for i in range(3)]
        return Y, Yi

    def hessian_tail(self, wb, n0):
        Y, Yi = self.Y_Yi_jets(wb)
        pi = arb.pi()
        trY = Y[0][0].v + Y[1][1].v + Y[2][2].v
        trYi = Yi[0][0].v + Yi[1][1].v + Yi[2][2].v
        t1 = _family_tail(Y, trYi, n0, pi)
        t2 = _family_tail(Yi, trY, n0, pi)
        if t1 is None or t2 is None:
            return None
        return t1 + t2
