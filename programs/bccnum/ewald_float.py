"""Floating-point Ewald energies (used only to steer searches and as a cross-check).

Deliberately an independent implementation of the formula in ewald_cert.py: Cartesian
coordinates, float64, no shell grouping, scipy's erfc, cut-offs by float comparison. It is used
(a) as a cross-check of the certified code, (b) for continuous parameter scans (hcp c/a).
"""

import math

import numpy as np
from scipy.special import erfc

from .exact import inv3, mat, matvec


def ewald_energy_float(B, positions, charges, alpha, R, K):
    """Ewald energy per cell. B: 3x3 array, COLUMNS are primitive vectors (Cartesian).

    positions: n x 3 Cartesian, charges: n. alpha, R, K floats (same length units as B).
    Same formula as ewald_cert.ewald_energy (real + reciprocal + self + background).
    """
    B = np.asarray(B, float)
    inverse = inv3(mat(B))
    frac = [matvec(inverse, p) for p in mat(positions)]
    return _fractional_energy(B, frac, charges, alpha, R, K)


def _fractional_energy(B, frac, charges, alpha, R, K):
    q = np.asarray(charges, float)
    V = abs(np.linalg.det(B))
    Binv = np.linalg.inv(B)
    G = 2 * math.pi * Binv.T                     # columns: reciprocal primitive vectors
    # Periodic equality is exact for the supplied coordinates. Keep distinct
    # fractional sites separate until their pair displacement has been reduced.
    basis = mat(B)
    frac = [tuple(x % 1 for x in p) for p in frac]
    if len(set(frac)) != len(frac):
        raise ValueError("coincident charges modulo the period lattice")
    # real space
    nmax = [int(math.ceil(np.linalg.norm(Binv[k]) * R)) + 2 for k in range(3)]
    rng = [np.arange(-m, m + 1) for m in nmax]
    mm = np.stack(np.meshgrid(*rng, indexing="ij"), -1).reshape(-1, 3)
    L = mm @ B.T
    nonzero_image = np.any(mm != 0, axis=1)
    E_real = 0.0
    for i in range(len(q)):
        for j in range(len(q)):
            delta = [a - b for a, b in zip(frac[i], frac[j])]
            centered = [x - round(x) for x in delta]
            d = L + np.asarray(matvec(basis, centered), dtype=float)
            r = np.hypot.reduce(d, axis=1)
            sel = r <= R
            if i == j:
                sel &= nonzero_image
            E_real += 0.5 * q[i] * q[j] * np.sum(erfc(alpha * r[sel]) / r[sel])
    # reciprocal space
    hmax = [int(math.ceil(np.linalg.norm(B[:, k]) * K / (2 * math.pi))) + 2 for k in range(3)]
    rng = [np.arange(-m, m + 1) for m in hmax]
    hh = np.stack(np.meshgrid(*rng, indexing="ij"), -1).reshape(-1, 3)
    Gv = hh @ G.T
    g2 = np.einsum("ij,ij->i", Gv, Gv)
    sel = np.any(hh != 0, axis=1) & (g2 <= K * K)
    g2 = g2[sel]
    S = np.exp(2j * math.pi * hh[sel] @ np.asarray(frac, dtype=float).T) @ q
    E_rec = 2 * math.pi / V * np.sum(np.exp(-g2 / (4 * alpha ** 2)) / g2 * np.abs(S) ** 2)
    E_self = -alpha / math.sqrt(math.pi) * np.sum(q * q)
    E_bg = -math.pi * q.sum() ** 2 / (2 * V * alpha ** 2)
    return E_real + E_rec + E_self + E_bg


def ws_scale(B, n):
    V = abs(np.linalg.det(np.asarray(B, float)))
    return (4 * math.pi * n / (3 * V)) ** (1 / 3)


def ocp_energy_ws_float(B, frac, alpha_ws=1.1, X=60.0):
    """OCP (unit charges, uniform background) energy per particle in e^2/a, a = WS radius."""
    B = np.asarray(B, float)
    n = len(frac)
    s = ws_scale(B, n)
    Bw = B * s
    alpha = alpha_ws
    R = math.sqrt(X) / alpha
    K = 2 * alpha * math.sqrt(X)
    return _fractional_energy(Bw, mat(frac), np.ones(n), alpha, R, K) / n


def hcp_cart(gamma):
    """hcp primitive vectors (columns) with a = 1, c/a = gamma; and fractional basis."""
    B = np.array([[1.0, -0.5, 0.0], [0.0, math.sqrt(3) / 2, 0.0], [0.0, 0.0, gamma]])
    frac = [[0, 0, 0], [1 / 3, 2 / 3, 1 / 2]]
    return B, frac


def cubic_cart(name):
    h = 0.5
    if name == "sc":
        return np.eye(3), [[0, 0, 0]]
    if name == "bcc":
        return np.array([[-h, h, h], [h, -h, h], [h, h, -h]]).T, [[0, 0, 0]]
    if name == "fcc":
        return np.array([[0, h, h], [h, 0, h], [h, h, 0]]).T, [[0, 0, 0]]
    raise KeyError(name)
