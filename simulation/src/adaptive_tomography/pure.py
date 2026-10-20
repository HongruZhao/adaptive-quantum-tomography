"""Algorithm 3: complete phase-paired effects, ridge fitting and tangent correction."""
import numpy as np
from .schedules import validated_batch_sizes
from .estimators import (OutcomeBatch, householder_frame, hermitian_basis,
                         least_squares_from_batches, weighted_tangent_update, top_vector,
                         validated_horizons)


def reference_measurement(D):
    eye = np.eye(D, dtype=complex)
    bases = [eye.copy()]
    for r in range(D):
        for s in range(r + 1, D):
            for phase in [1, 1j]:
                basis = eye.copy()
                basis[:, r] = (eye[:, r] + phase * eye[:, s]) / np.sqrt(2)
                basis[:, s] = (eye[:, r] - phase * eye[:, s]) / np.sqrt(2)
                bases.append(basis)
    bases = np.array(bases)
    w = np.arange(1, D + 1, dtype=float)
    w /= np.linalg.norm(w)
    u = w - eye[:, 0]
    rotate = eye - 2 * np.outer(u, u.conj()) / np.vdot(u, u)
    bases = rotate @ bases
    B = len(bases)
    assert B == D*D - D + 1
    seed = np.array([np.outer(v, v.conj()) / B
                     for basis in bases for v in basis.T])
    V = np.diag(np.r_[1j, np.ones(D-1)])
    paired = np.concatenate([seed/2, (V.conj().T @ seed @ V)/2])
    labels = np.array([(b, ell, k) for b in range(2)
                       for ell in range(B) for k in range(D)], dtype=int)
    return paired, bases, labels


def tangent_basis(h):
    complement = householder_frame(h)[:, 1:]
    return np.array([np.outer(v, h.conj()) + np.outer(h, v.conj())
                     for phase in [1, 1j]
                     for v in (phase * complement.T / np.sqrt(2))])


def information(effects, h, tangent):
    p = np.einsum('i,aij,j->a', h.conj(), effects, h).real
    g = np.einsum('aij,kji->ak', effects, tangent).real
    positive = p > 0
    return g[positive].T @ (g[positive] / p[positive, None])


def preliminary(gram, rhs, hb):
    raw = np.einsum('k,kij->ij', np.linalg.solve(gram, rhs), hb)
    return top_vector(raw)


def correction(h, records, reference, ridge=1.0):
    """Same clipped tangent normal equation, assembled in one array."""
    D = len(h)
    d = D - 1
    complement = householder_frame(h)[:, 1:]
    effects = np.concatenate([r.effects for r in records])
    counts = np.concatenate([r.counts for r in records])
    copies = np.concatenate([np.full(len(r.counts), r.counts.sum()) for r in records])
    Eh = effects @ h
    q = (Eh @ h.conj()).real
    amplitudes = Eh.conj() @ complement
    gradient = np.sqrt(2)*np.concatenate([amplitudes.real, -amplitudes.imag], axis=1)
    floor = np.min(reference[:, 0, 0].real)/4
    weights = np.maximum(q, floor)
    matrix = ridge*np.eye(2*d) + gradient.T @ ((copies/weights)[:, None]*gradient)
    score = gradient.T @ ((counts - copies*q)/weights)
    step = np.linalg.solve(matrix, score)
    delta_h = complement @ (step[:d] + 1j*step[d:]) / np.sqrt(2)
    result = h + delta_h
    return result/np.linalg.norm(result)


def physical_losses(truth, vector, n):
    phase = np.vdot(truth, vector)
    aligned = vector*np.conj(phase)/abs(phase) if abs(phase) else vector
    diff = aligned - truth
    bures = float(np.vdot(diff, diff).real)
    P0 = np.outer(truth, truth.conj())
    P = np.outer(vector, vector.conj())
    frobenius = float(np.linalg.norm(P-P0)**2)
    assert abs(frobenius - (2*bures - bures*bures/2)) < 2e-12
    return [n*frobenius, n*bures]


def validate_reference(reference, bases, h0):
    D = len(h0)
    hb = hermitian_basis(D)
    features = np.einsum('aij,kji->ak', reference, hb).real
    href = np.eye(D, dtype=complex)[:, 0]
    tangent = tangent_basis(href)
    target = information(reference, href, tangent)
    frame = features.T @ features
    checks = {
        'basis_orthonormality_error': float(np.linalg.norm(bases.conj().transpose(0,2,1)@bases-np.eye(D))),
        'completeness_error': float(np.linalg.norm(reference.sum(0)-np.eye(D))),
        'minimum_effect_eigenvalue': float(np.linalg.eigvalsh(reference).min()),
        'minimum_reference_probability': float(reference[:,0,0].real.min()),
        'ambient_frame_rank': int(np.linalg.matrix_rank(features)),
        'minimum_frame_eigenvalue': float(np.linalg.eigvalsh(frame).min()),
        'fisher_identity_error_in_Frobenius_tangent_frame': float(np.linalg.norm(target-np.eye(2*(D-1)))),
    }
    assert checks['ambient_frame_rank'] == D*D
    assert checks['minimum_reference_probability'] > 0
    assert checks['minimum_frame_eigenvalue'] > 0
    assert checks['minimum_effect_eigenvalue'] > -1e-12
    assert all(v < 1e-10 for k,v in checks.items() if k.endswith('error') or k.endswith('frame'))
    # Independent derivative check on normalized states in the true tangent frame.
    true_tangent = tangent_basis(h0)
    analytic = np.einsum('aij,kji->ak', reference, true_tangent).real
    numeric = []
    eps = 1e-6
    for direction in true_tangent:
        v = direction @ h0
        plus = h0 + eps*v
        minus = h0 - eps*v
        plus /= np.linalg.norm(plus)
        minus /= np.linalg.norm(minus)
        p_plus = np.einsum('i,aij,j->a', plus.conj(), reference, plus).real
        p_minus = np.einsum('i,aij,j->a', minus.conj(), reference, minus).real
        numeric.append((p_plus-p_minus)/(2*eps))
    checks['finite_difference_gradient_max_error'] = float(np.max(abs(np.array(numeric).T-analytic)))
    assert checks['finite_difference_gradient_max_error'] < 1e-8
    return checks


def trajectory(D, reference, truth, rng, horizons, diagnostic=False, validate=False, ridge=1.0, correction_ridge=1.0, batch_sizes=None):
    horizons = validated_horizons(horizons)
    sizes = validated_batch_sizes(batch_sizes, horizons)
    hb = hermitian_basis(D)
    gram = ridge*np.eye(D*D)
    rhs = np.zeros(D*D)
    h = np.eye(D, dtype=complex)[:, 0]
    records = []
    losses = np.zeros((len(horizons), 2, 2))
    errors = np.zeros((len(horizons), 2, 2*(D-1)))
    P0 = np.outer(truth, truth.conj())
    tangent = tangent_basis(truth)
    accumulated = np.zeros((2*(D-1), 2*(D-1)))
    diagnostics = []
    n = 0
    for size in sizes.tolist():
        U = householder_frame(h)
        effects = U @ reference @ U.conj().T
        p = np.einsum('i,aij,j->a', truth.conj(), effects, truth).real
        assert p.min() >= -1e-12 and abs(p.sum()-1) < 1e-10
        p = np.maximum(p, 0)
        counts = rng.multinomial(size, p/p.sum())
        records.append(OutcomeBatch(effects, counts))
        features = np.einsum('aij,kji->ak', effects, hb).real
        gram += size*features.T@features
        rhs += features.T@counts
        if diagnostic:
            accumulated += size*information(effects, truth, tangent)
        h = preliminary(gram, rhs, hb)
        n += size
        if n not in horizons:
            continue
        ix = int(np.flatnonzero(horizons == n)[0])
        corrected = correction(h, records, reference, correction_ridge)
        if validate and n in [256, 4096, 65536, int(horizons[-1])]:
            literal = least_squares_from_batches(records, D, ridge)
            assert np.linalg.norm(np.outer(h,h.conj()) - literal['state']) < 1e-9
            direct = weighted_tangent_update(h, records, reference, correction_ridge)
            assert np.linalg.norm(np.outer(corrected, corrected.conj())-direct['state']) < 1e-9
            reversed_fit = weighted_tangent_update(h, list(reversed(records)), reference, correction_ridge)
            assert np.linalg.norm(reversed_fit['state']-direct['state']) < 1e-9
            assert direct['copies_used'] == n == sum(r.counts.sum() for r in records)
        for method, vector in enumerate([h, corrected]):
            assert abs(np.vdot(vector,vector).real-1) < 1e-12
            losses[ix, method] = physical_losses(truth, vector, n)
            P = np.outer(vector, vector.conj())
            errors[ix, method] = np.sqrt(n)*np.einsum("kij,ji->k", tangent, P-P0).real
        if diagnostic:
            U_next = householder_frame(h)
            current = information(U_next@reference@U_next.conj().T, truth, tangent)
            average = accumulated/n
            cf = float(np.trace(np.linalg.inv(current)))
            af = float(np.trace(np.linalg.inv(average)))
            diagnostics.append({'n': n, 'current_frobenius': cf, 'average_frobenius': af,
                'current_bures': cf/2, 'average_bures': af/2,
                'current_information': current.tolist(), 'average_information': average.tolist(),
                'current_operator_norm_error': float(np.linalg.norm(current-np.eye(2*(D-1)), 2)),
                'average_operator_norm_error': float(np.linalg.norm(average-np.eye(2*(D-1)), 2))})
    return losses, errors, diagnostics


