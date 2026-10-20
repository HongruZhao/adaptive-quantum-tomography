"""Optional finite measurement for the same-record covariance comparison."""
import numpy as np
from .estimators import hermitian_basis
from .pure import tangent_basis


def reference_measurement(D):
    eye = np.eye(D, dtype=complex)
    phases = [1, 1j, -1, -1j]
    library = [eye[j] for j in range(1, D)]
    for j in range(1, D):
        for k in range(1, D):
            for phase in phases:
                library.append(eye[j] if j == k else
                               (eye[j] + phase * eye[k]) / np.sqrt(2))
    L = len(library)
    c = D / (8 * L)
    effects = []
    for t in [1 / (2 * D), 3 / (2 * D)]:
        for phase in phases:
            for v in library:
                w = np.sqrt(t) * eye[0] + phase * np.sqrt(1 - t) * v
                effects.append(c * np.outer(w, w.conj()))
    return np.asarray(effects)


def check_reference(effects):
    D = effects.shape[1]
    h = np.eye(D, dtype=complex)[:, 0]
    tangent = tangent_basis(h)
    hb = hermitian_basis(D)
    p = effects[:, 0, 0].real
    f = np.einsum('aij,kji->ak', effects, hb).real
    g = np.einsum('aij,kji->ak', effects, tangent).real
    info = g.T @ (g / p[:, None])
    gram = g.T @ g
    mean = g.T @ p
    noise = g.T @ (p[:, None] * g) - np.outer(mean, mean)
    d = D - 1
    L = d * (4 * d + 1)
    alpha = (4 * D - 5) / (32 * L * d)
    beta = (5 * D - 7) / (256 * L**2 * d)
    v = 4 * d * (5 * D - 7) / (4 * D - 5)**2
    checks = {
        'completeness_error': float(np.linalg.norm(effects.sum(axis=0) - np.eye(D))),
        'minimum_frame_eigenvalue': float(np.linalg.eigvalsh(f.T @ f).min()),
        'minimum_reference_probability': float(p.min()),
        'fisher_identity_error': float(np.linalg.norm(info - np.eye(2*d))),
        'tangent_gram_error': float(np.linalg.norm(gram - alpha*np.eye(2*d))),
        'tangent_noise_error': float(np.linalg.norm(noise - beta*np.eye(2*d))),
        'sandwich_target_error': float(np.linalg.norm(
            np.linalg.solve(gram, np.linalg.solve(gram, noise).T).T - v*np.eye(2*d))),
        'number_of_labelled_effects': len(effects),
    }
    assert checks['minimum_frame_eigenvalue'] > 0
    assert p.min() > 0
    assert all(value < 1e-10 for key, value in checks.items() if key.endswith('error'))
    return checks


