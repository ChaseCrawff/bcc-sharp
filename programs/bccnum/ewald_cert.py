r"""Certified Ewald energy of a periodic point-charge configuration (+ neutralizing background).

Energy computed (per period cell, natural units; Lambda = B Z^3, basis s_j = B f_j, charges q_j,
cell volume V = sqrt(det M), total charge Q = sum q_j, Ewald parameter alpha > 0):

    E_cell = 1/2 sum_{i,j} sum'_{L in Lambda} q_i q_j erfc(alpha |s_i - s_j + L|) / |s_i - s_j + L|
           + (2 pi / V) sum_{G in Lambda^*, G != 0} exp(-|G|^2 / (4 alpha^2)) / |G|^2 |sum_j q_j e^{i G.s_j}|^2
           - (alpha / sqrt(pi)) sum_j q_j^2
           - pi Q^2 / (2 V alpha^2)                                   (uniform neutralizing background)

(sum' omits L = 0 when i = j.) E_cell does not depend on alpha (constants.py checks this:
two different alpha must give overlapping enclosures). For Q != 0 this is the energy of the point
charges in a uniform background of total charge -Q per cell, with the G = 0 Fourier mode removed
("tinfoil"/periodic convention); it equals W/N * n for the periodic (torus) jellium energy W
evaluated at the perfect lattice on any commensurate torus.

Everything except the final transcendental sums is exact:
  * squared distances |B v|^2 = v^T M v and |G|^2 / (4 pi^2) = h^T M^{-1} h are exact rationals,
  * the enumeration of lattice points inside the cut-off balls uses exact integer comparisons,
  * points are grouped into exact shells, so erfc/exp are evaluated once per shell in arb,
  * phases G.s_j = 2 pi h.f_j are rational multiples of 2 pi; cosines are exact when rational
    (Niven) and arb otherwise.
Truncation errors (all lattice points with |p| > R, all G with |G| > K) are bounded by
`intervals.lattice_tail_bound` (packing count + summation by parts + Gaussian tail bounds).
The result is an arb ball that contains the exact E_cell.
"""

import time
from fractions import Fraction as Fr

import numpy as np
from flint import arb, ctx

from .exact import inv3, det3, integerize, common_denominator, isqrt_ceil_frac, cos2pi_rational, F
from .intervals import arb_of, lattice_tail_bound

_INT64_SAFE = 2 ** 62


def _box(T):
    return np.arange(-T, T + 1, dtype=np.int64)


def _grid(T0, T1, T2):
    g = np.stack(np.meshgrid(_box(T0), _box(T1), _box(T2), indexing="ij"), axis=-1)
    return g.reshape(-1, 3)


def _quadform_int(Ai, V):
    """Row-wise v^T Ai v for integer matrix Ai (3x3 tuple) and int64 array V (N x 3)."""
    A = np.array(Ai, dtype=np.int64)
    return np.einsum("ni,ij,nj->n", V, A, V)


def shortest_vector_sq(M):
    """Exact min_{m in Z^3, m != 0} m^T M m for a positive definite rational Gram matrix M.

    Any m with m^T M m <= lam^2 satisfies |m_k| <= sqrt((M^{-1})_kk) * lam, and
    lam^2 <= min_k M_kk, so the enumeration box below provably contains a shortest vector.
    """
    Minv = inv3(M)
    lam_up2 = min(M[k][k] for k in range(3))
    T = [isqrt_ceil_frac(Minv[k][k] * lam_up2) for k in range(3)]
    D, Mi = integerize(M)
    _check_overflow(Mi, max(T))          # guard against int64 overflow
    V = _grid(*T)
    V = V[np.any(V != 0, axis=1)]
    q = _quadform_int(Mi, V)
    return Fr(int(q.min()), D)


def _int_threshold(num, den):
    """Exact integer threshold for the test q * den <= num with q a nonnegative int64 and den > 0.

    For integer q this test is equivalent to q <= floor(num / den), which needs no product. The result is clamped to
    _INT64_SAFE: every q passed the _check_overflow guard, so q < _INT64_SAFE, and the clamp changes no comparison.
    (The product q * den computed in int64 without a guard could wrap around; this form avoids the product.)
    """
    num, den = int(num), int(den)
    assert den > 0
    return min(num // den, _INT64_SAFE) if num >= 0 else -1


def _check_overflow(Ai, maxabs):
    bound = 9 * max(abs(x) for r in Ai for x in r) * maxabs * maxabs
    if bound >= _INT64_SAFE:
        raise OverflowError("integer enumeration would overflow int64; reduce denominators")


def pair_classes(struct):
    """Group ordered pairs (i,j) by the class of f_i - f_j mod Z^3.

    Returns (df, {c: w}) with c an integer 3-tuple in [0, df)^3 representing df*(f_i - f_j mod 1)
    and w = sum of q_i q_j over the pairs in that class (exact int).
    """
    df = common_denominator(x for f in struct.frac for x in f)
    C = [tuple(int(x * df) for x in f) for f in struct.frac]
    classes = {}
    for i, ci in enumerate(C):
        for j, cj in enumerate(C):
            key = tuple((a - b) % df for a, b in zip(ci, cj))
            if i != j and not any(key):
                raise ValueError("coincident charges modulo the period lattice")
            classes[key] = classes.get(key, 0) + struct.charges[i] * struct.charges[j]
    return df, classes


def real_space_shells(struct, R2):
    """Exact real-space shells inside |p|^2 <= R2 (natural units).

    Returns (Dr, shells, npoints, signed) where shells = {n: w} means: the points with
    |p|^2 = n / Dr carry total weight w = sum q_i q_j (exact Fraction), over all ordered pairs,
    excluding p = 0 for i = j (self term). `signed` = (P_plus, P_minus): sums of positive and of
    |negative| pair weights q_i q_j (used for the sign of the tail enclosure).
    """
    R2 = F(R2)
    M = struct.gram
    Minv = inv3(M)
    D, Mi = integerize(M)
    df, classes = pair_classes(struct)
    Dr = D * df * df
    thr_num, thr_den = R2.numerator * Dr, R2.denominator   # include iff q * thr_den <= thr_num
    T = [isqrt_ceil_frac(Minv[k][k] * R2) + 1 for k in range(3)]   # |m_k + f_k| <= sqrt(Minv_kk R2), |f_k| < 1
    base = _grid(*T)
    _check_overflow(Mi, (max(T) + 1) * df)
    shells = {}
    npoints = 0
    p_plus = sum(w for w in classes.values() if w > 0)
    p_minus = -sum(w for w in classes.values() if w < 0)
    for c, w in classes.items():
        if w == 0:
            continue
        V = base * df + np.array(c, dtype=np.int64)
        q = _quadform_int(Mi, V)
        keep = (q <= _int_threshold(thr_num, thr_den))
        if all(x == 0 for x in c):
            keep &= (q != 0)           # omit the self term L = 0
        vals, counts = np.unique(q[keep], return_counts=True)
        npoints += int(counts.sum())
        for v, cnt in zip(vals.tolist(), counts.tolist()):
            shells[v] = shells.get(v, 0) + w * cnt
    return Dr, {k: Fr(v) for k, v in shells.items() if v != 0}, npoints, (p_plus, p_minus)


def reciprocal_shells(struct, kappa):
    """Exact reciprocal shells: h != 0 with h^T M^{-1} h <= kappa (i.e. |G| <= 2 pi sqrt(kappa)).

    Returns (Dg, shells, npoints, exact) with shells = {n: w}: the G with |G|^2 = 4 pi^2 n / Dg carry
    total weight w = sum_h |S(h)|^2, S(h) = sum_j q_j exp(2 pi i h.f_j). w is an exact Fraction if
    all needed cosines are rational (exact=True), else an arb.
    """
    kappa = F(kappa)
    M = struct.gram
    Minv = inv3(M)
    Dg, Minvi = integerize(Minv)
    T = [isqrt_ceil_frac(M[k][k] * kappa) for k in range(3)]   # |h_k| <= sqrt(M_kk kappa)
    _check_overflow(Minvi, max(T) + 1)
    H = _grid(*T)
    q = _quadform_int(Minvi, H)
    keep = (q <= _int_threshold(kappa.numerator * Dg, kappa.denominator)) & (q != 0)
    H, q = H[keep], q[keep]
    df, classes = pair_classes(struct)
    cos_exact = [cos2pi_rational(Fr(p, df)) for p in range(df)]
    exact = all(c is not None for c in cos_exact)
    if exact:
        cos_vals = cos_exact
    else:
        cos_vals = [(2 * arb(p) / df * arb.pi()).cos() for p in range(df)]
    # |S(h)|^2 = sum_classes w_c cos(2 pi h.c / df)
    shells = {}
    uq, inv = np.unique(q, return_inverse=True)
    acc = [Fr(0) if exact else arb(0) for _ in range(len(uq))]
    for c, w in classes.items():
        if w == 0:
            continue
        ph = (H @ np.array(c, dtype=np.int64)) % df
        # counts per (shell, phase)
        key = inv.astype(np.int64) * df + ph
        kv, kc = np.unique(key, return_counts=True)
        for kk, cnt in zip(kv.tolist(), kc.tolist()):
            s, p = divmod(kk, df)
            acc[s] += w * cnt * cos_vals[p]
    for s, nval in enumerate(uq.tolist()):
        shells[nval] = acc[s]
    return Dg, shells, int(len(q)), exact


def ewald_energy(struct, alpha, R2, kappa, prec=256):
    """Certified Ewald energy. alpha, R2, kappa exact rationals (natural units).

    alpha : Ewald splitting parameter.
    R2    : real-space cut-off radius squared; all points with |p|^2 <= R2 are summed exactly.
    kappa : reciprocal cut-off, all G with |G|^2 <= 4 pi^2 kappa are summed exactly.
    Returns a dict of arb enclosures and bookkeeping.
    """
    t0 = time.perf_counter()
    old = ctx.prec
    ctx.prec = prec
    try:
        alpha, R2, kappa = F(alpha), F(R2), F(kappa)
        M = struct.gram
        Minv = inv3(M)
        detM = det3(M)
        pi = arb.pi()
        V = arb_of(detM).sqrt()
        a = arb_of(alpha)
        q = struct.charges
        Q = sum(q)
        sum_q2 = sum(x * x for x in q)
        sum_abs = sum(abs(x) for x in q)

        Dr, rshells, n_real, (p_plus, p_minus) = real_space_shells(struct, R2)
        Dg, gshells, n_rec, phases_exact = reciprocal_shells(struct, kappa)

        S_real = arb(0)
        for nval, w in rshells.items():
            r = (arb(nval) / Dr).sqrt()
            S_real += arb_of(w) * (a * r).erfc() / r
        E_real_trunc = S_real / 2

        S_rec = arb(0)
        for nval, w in gshells.items():
            if w == 0:
                continue
            g2 = 4 * pi * pi * arb(nval) / Dg
            S_rec += arb_of(w) * (-g2 / (4 * a * a)).exp() / g2
        E_rec_trunc = 2 * pi / V * S_rec

        E_self = -a / pi.sqrt() * sum_q2
        E_bg = -pi * Q * Q / (2 * V * a * a)

        # ---- rigorous truncation bounds ----
        lam2 = shortest_vector_sq(M)                 # real lattice, natural units
        lam2s = shortest_vector_sq(Minv)             # reciprocal: |G|^2 = 4 pi^2 * h^T M^{-1} h
        rho = arb_of(lam2).sqrt() / 2
        rho_s = pi * arb_of(lam2s).sqrt()            # = (2 pi sqrt(lam2s)) / 2
        R = arb_of(R2).sqrt()
        K = 2 * pi * arb_of(kappa).sqrt()
        # each translate sum: sum_{|p|>R} erfc(a|p|)/|p| <= tail(g = e^{-a^2 r^2}/(a sqrt(pi) r^2))
        B_real = lattice_tail_bound(rho, R, 1 / (a * pi.sqrt()), 2, a * a)
        B_rec = lattice_tail_bound(rho_s, K, arb(1), 2, 1 / (4 * a * a))
        B_real_u = arb(B_real.upper())
        B_rec_u = arb(B_rec.upper())
        # real tail in [-(P_minus/2) B, (P_plus/2) B]; reciprocal tail in [0, (2pi/V) (sum|q|)^2 B]
        real_lo, real_hi = -arb(p_minus) / 2 * B_real_u, arb(p_plus) / 2 * B_real_u
        rec_hi = arb((2 * pi / V * sum_abs ** 2 * B_rec_u).upper())
        tail_real = arb(real_lo.lower()).union(arb(real_hi.upper()))
        tail_rec = arb(0).union(rec_hi)

        E_cell = E_real_trunc + tail_real + E_rec_trunc + tail_rec + E_self + E_bg
        n = struct.n
        per_particle = E_cell / n
        s = (4 * pi * n / (3 * V)) ** (arb(1) / 3)   # natural -> Wigner-Seitz length scale
        per_particle_ws = per_particle / s
        return {
            "E_cell_nat": E_cell,
            "E_per_particle_nat": per_particle,
            "E_per_particle_ws": per_particle_ws,     # units e^2/a, a = Wigner-Seitz radius
            "parts": {"real_truncated": E_real_trunc, "real_tail": tail_real,
                      "reciprocal_truncated": E_rec_trunc, "reciprocal_tail": tail_rec,
                      "self": E_self, "background": E_bg},
            "tail_bound_real_per_translate": B_real_u,
            "tail_bound_reciprocal_lattice_sum": B_rec_u,
            "scale_nat_to_ws": s,
            "cell_volume_nat": V,
            "shortest_vector_sq": str(lam2),
            "shortest_reciprocal_sq_over_4pi2": str(lam2s),
            "n_real_points": n_real, "n_real_shells": len(rshells),
            "n_reciprocal_points": n_rec, "n_reciprocal_shells": len(gshells),
            "phases_exact": phases_exact,
            "alpha": str(alpha), "R2": str(R2), "kappa": str(kappa), "prec_bits": prec,
            "seconds": time.perf_counter() - t0,
        }
    finally:
        ctx.prec = old


def default_cutoffs(struct, alpha_ws, X):
    """Exact (alpha, R2, kappa) for a target exponent X: alpha^2 R^2 >= X and K^2/(4 alpha^2) >= X.

    alpha_ws is the splitting parameter in Wigner-Seitz units (alpha_nat = alpha_ws * s).
    All three returned values are exact rationals (alpha rounded to 1/1000).
    """
    import math
    V = math.sqrt(float(det3(struct.gram)))
    s = (4 * math.pi * struct.n / (3 * V)) ** (1 / 3)
    alpha = Fr(round(alpha_ws * s * 1000), 1000)
    R2 = Fr(X) / (alpha * alpha)
    kappa_f = float(alpha) ** 2 * X / math.pi ** 2
    kappa = Fr(math.ceil(kappa_f * 10 ** 6) + 1, 10 ** 6)
    # (X only steers the cut-offs; rigour never depends on it: the tail bounds are computed
    #  from the exact R2 and kappa actually used.)
    return alpha, R2, kappa
