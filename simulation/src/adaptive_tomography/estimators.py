"""Symmetric, all-data tangent GLS for the main paper's P2 estimator.

The existing ridge LS estimate and the weighted correction use the same
complete collection of measurement/count records. No prefix is selected.
The returned state is unchanged by permuting records in exact arithmetic.
Floating-point evaluation is a reference implementation, not a Lean proof.
"""
from dataclasses import dataclass
import numpy as np


def validated_horizons(horizons):
    """Validate integer reporting sizes; the batch validator checks reachability."""
    values = np.asarray(horizons)
    if values.ndim != 1 or len(values) == 0 or not np.issubdtype(values.dtype, np.integer):
        raise ValueError('Reporting horizons must be a nonempty integer vector.')
    if np.any(values < 16) or np.any(np.diff(values) <= 0):
        raise ValueError('Reporting horizons must be increasing integers, at least 16.')
    return values.astype(np.int64, copy=False)


@dataclass
class OutcomeBatch:
    effects: np.ndarray  # (outcomes, D, D), full actual labelled POVM
    counts: np.ndarray   # observed counts for this setting


def householder_frame(vector):
    """The paper's exact Householder formula, evaluated numerically."""
    h = np.asarray(vector, dtype=complex)
    h = h / np.linalg.norm(h)
    gamma = h[0] / abs(h[0]) if abs(h[0]) else 1.0
    v = gamma.conjugate() * h
    v = v.copy()
    v[0] += 1.0
    return gamma * (2 * np.outer(v, v.conj()) / np.vdot(v, v).real - np.eye(len(h)))


def phase_pair(seed_effects):
    """Labelled effects F_y/2 and V* F_y V/2, exactly as in the paper."""
    effects = np.asarray(seed_effects, dtype=complex)
    dimension = effects.shape[1]
    v = np.diag(np.r_[1j, np.ones(dimension - 1)])
    return np.concatenate((effects / 2, (v.conj().T @ effects @ v) / 2))


def probabilities_and_gradients(effects, initial_vector, complement=None):
    """Born masses and QFI-normalized chart derivatives at a pure vector.

    Multiplying these derivatives by sqrt(2) gives derivatives in the
    Frobenius-orthonormal tangent basis used by weighted_tangent_update.
    """
    h = np.asarray(initial_vector, dtype=complex)
    h = h / np.linalg.norm(h)
    if complement is None:
        complement = householder_frame(h)[:, 1:]
    q = np.einsum('i,aij,j->a', h.conj(), effects, h).real
    a = np.einsum('i,aij,jk->ak', h.conj(), effects, complement)
    return q, np.concatenate((a.real, -a.imag), axis=1), complement


def _record(batch, dimension):
    effects = np.asarray(batch.effects, dtype=complex)
    counts = np.asarray(batch.counts, dtype=float)
    if counts.ndim != 1 or effects.shape != (len(counts), dimension, dimension):
        raise ValueError('Effect and count shapes do not match.')
    if not np.all(np.isfinite(counts)) or np.any(counts < 0):
        raise ValueError('Counts must be finite and nonnegative.')
    return effects, counts


def weighted_tangent_update(initial_vector, batches, reference_effects,
                            ridge=1.0, complement=None):
    """One all-data GLS correction from the paper's tangent quadratic.

    ridge is eta multiplying the Frobenius tangent penalty. Step coordinates
    use a Frobenius-orthonormal real basis, so the ideal limiting information
    matrix per copy is the identity. Pass all records, with weights evaluated
    at the same final full-data initial estimate.
    """
    h = np.asarray(initial_vector, dtype=complex)
    h = h / np.linalg.norm(h)
    d = len(h) - 1
    if d < 1 or not ridge > 0:
        raise ValueError('Require D >= 2 and a positive ridge.')
    floor = float(np.min(np.asarray(reference_effects)[:, 0, 0].real)) / 4
    if not np.isfinite(floor) or floor <= 0:
        raise ValueError('The reference POVM must have positive reference masses.')
    if complement is None:
        complement = householder_frame(h)[:, 1:]
    matrix = ridge * np.eye(2 * d)
    score = np.zeros(2 * d)
    copies_used = 0.0
    clipped = 0
    for batch in batches:
        effects, counts = _record(batch, d + 1)
        q, gradient, _ = probabilities_and_gradients(effects, h, complement)
        gradient = np.sqrt(2.0) * gradient
        weights = np.maximum(q, floor)
        copies = float(counts.sum())
        matrix += copies * gradient.T @ (gradient / weights[:, None])
        score += gradient.T @ ((counts - copies * q) / weights)
        copies_used += copies
        clipped += int(np.count_nonzero(q < floor))
    if copies_used <= 0:
        raise ValueError('At least one observation is required.')
    step = np.linalg.solve(matrix, score)
    tangent_vector = complement @ (step[:d] + 1j * step[d:]) / np.sqrt(2.0)
    delta = np.outer(tangent_vector, h.conj()) + np.outer(h, tangent_vector.conj())
    estimate = h + tangent_vector
    estimate /= np.linalg.norm(estimate)
    return {'vector': estimate, 'state': np.outer(estimate, estimate.conj()),
            'tangent_correction': delta, 'step': step,
            'matrix': matrix, 'score': score,
            'probability_floor': floor, 'copies_used': copies_used,
            'clipped_batch_outcomes': clipped}


def hermitian_basis(dimension):
    """A Frobenius-orthonormal real basis of Herm(C^D)."""
    eye = np.eye(dimension, dtype=complex)
    basis = [np.outer(e, e.conj()) for e in eye]
    for j in range(dimension):
        for k in range(j + 1, dimension):
            a = np.outer(eye[j], eye[k])
            basis += [(a + a.T) / np.sqrt(2), 1j * (a - a.T) / np.sqrt(2)]
    return np.asarray(basis)


def least_squares_from_batches(batches, dimension, ridge=1.0):
    """Existing all-observation ridge LS, followed by a nearest pure state.

    This ambient D^2-dimensional solve is the original preliminary estimator;
    its cost is separate from the additional 2(D-1)-dimensional GLS correction.
    """
    if dimension < 2 or not ridge > 0:
        raise ValueError('Require D >= 2 and a positive ridge.')
    basis = hermitian_basis(dimension)
    matrix = ridge * np.eye(dimension**2)
    rhs = np.zeros(dimension**2)
    copies_used = 0.0
    for batch in batches:
        effects, counts = _record(batch, dimension)
        features = np.einsum('aij,kji->ak', effects, basis).real
        copies = float(counts.sum())
        matrix += copies * features.T @ features
        rhs += features.T @ counts
        copies_used += copies
    if copies_used <= 0:
        raise ValueError('At least one observation is required.')
    coefficients = np.linalg.solve(matrix, rhs)
    raw = np.einsum('k,kij->ij', coefficients, basis)
    raw = (raw + raw.conj().T) / 2
    h = top_vector(raw)
    return {'raw': raw, 'vector': h, 'state': np.outer(h, h.conj()),
            'matrix': matrix, 'rhs': rhs, 'copies_used': copies_used}


def symmetric_gls_estimate(batches, reference_effects, ridge=1.0,
                           correction_ridge=1.0):
    """Compute both stages from every record, with no chronological split."""
    batches = list(batches)
    dimension = np.asarray(reference_effects).shape[1]
    initial = least_squares_from_batches(batches, dimension, ridge)
    corrected = weighted_tangent_update(initial['vector'], batches,
                                        reference_effects, correction_ridge)
    corrected['initial'] = initial
    return corrected


def top_vector(raw):
    """Largest-algebraic-eigenvalue vector with fixed tie and phase rules.

    For exactly equal computed largest eigenvalues, project successive
    coordinate vectors onto their eigenspace and use the first nonzero
    projection. Fix phase at the first maximum-modulus component. No
    near-eigenvalue threshold changes the mathematical estimator.
    """
    values, vectors = np.linalg.eigh((raw + raw.conj().T) / 2)
    selected = vectors[:, values == values[-1]]
    projector = selected @ selected.conj().T
    for column in projector.T:
        length = np.linalg.norm(column)
        if length > 0:
            h = column / length
            break
    pivot = int(np.argmax(abs(h)))
    return h * np.conj(h[pivot]) / abs(h[pivot])
