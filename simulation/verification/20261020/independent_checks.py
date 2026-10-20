"""Independent Oct 20 adversarial tests; never modifies production sources/data.

Dense least-squares solves, fixed-record replay and coordinate-equivariance
checks were written for this audit independently of the package unit tests.
"""
from pathlib import Path
from datetime import datetime, timezone
from zoneinfo import ZoneInfo
import contextlib
import hashlib
import io
import json
import sys
from unittest.mock import patch
import argparse
import numpy as np

SCRIPT = Path(__file__).resolve()
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--repo', type=Path, help='Path to the unchanged GitHub checkout')
parser.add_argument('--output', type=Path, help='New directory for fresh independent evidence')
args = parser.parse_args()
WORKSPACE = SCRIPT.parent.parents[4]
REPO = (args.repo or WORKSPACE/'GitHub/adaptive-quantum-tomography').resolve()
HERE = (args.output or SCRIPT.parent).resolve()
HERE.mkdir(parents=True, exist_ok=True)
ROOT = WORKSPACE
SIM = REPO / 'simulation'
sys.path.insert(0, str(SIM / 'src'))
from adaptive_tomography import mixed, pure, estimators, optional, simulation, schedules


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def sources():
    files = list((SIM / 'src').rglob('*.py')) + list((SIM / 'configs').glob('*.json'))
    files += list((SIM / 'tests').glob('*.py')) + list((REPO / 'lean').rglob('*.lean'))
    paper = ROOT / 'revisions/ejs_citation_review_20261006/source/paper/ejs'
    paper_files = list(paper.rglob('*.tex')) if paper.is_dir() else []
    repo_hashes = {'repo/'+str(p.relative_to(REPO)): sha(p) for p in sorted(files)}
    repo_hashes.update({'paper_source/'+str(p.relative_to(paper)): sha(p) for p in paper_files})
    if (REPO/'ejs_main.pdf').is_file():
        repo_hashes['repo/ejs_main.pdf'] = sha(REPO/'ejs_main.pdf')
    return repo_hashes


def P(h):
    return np.outer(h, h.conj())


def near(a, b, atol=2e-10, rtol=2e-10):
    np.testing.assert_allclose(a, b, atol=atol, rtol=rtol)


def normal(h):
    return h / np.linalg.norm(h)


def sqrtm(a):
    e, v = np.linalg.eigh((a + a.conj().T) / 2)
    assert e.min() >= -1e-10
    return (v * np.sqrt(np.maximum(e, 0))) @ v.conj().T


def full_bures(a, b):
    s = sqrtm(a)
    return 2 - 2 * np.trace(sqrtm(s @ b @ s)).real


def basis(D):
    # A separate construction of the real isometry Herm(C^D) -> R^(D^2).
    result = [np.diag(np.eye(D)[j]).astype(complex) for j in range(D)]
    for j in range(D):
        for k in range(j + 1, D):
            a = np.zeros((D, D), complex)
            a[j, k] = a[k, j] = 1 / np.sqrt(2)
            result.append(a)
            b = np.zeros((D, D), complex)
            b[j, k], b[k, j] = 1j / np.sqrt(2), -1j / np.sqrt(2)
            result.append(b)
    return np.array(result)


def paper_frame(h):
    # Explicit displayed formula, deliberately avoiding the package helper.
    g = h[0] / abs(h[0]) if h[0] != 0 else 1
    v = np.r_[1, np.zeros(len(h)-1)] + np.conj(g) * h
    return g * (2 * P(v) / np.vdot(v, v).real - np.eye(len(h)))


def tangent_frame(h):
    # Gram-Schmidt from coordinate vectors, not the production Householder.
    comp = []
    for e in np.eye(len(h), dtype=complex):
        v = e - h * np.vdot(h, e)
        for c in comp:
            v -= c * np.vdot(c, v)
        if np.linalg.norm(v) > 1e-8:
            comp.append(normal(v))
        if len(comp) == len(h)-1:
            break
    out = []
    for c in comp:
        for phase in [1, 1j]:
            v = phase * c / np.sqrt(2)
            out.append(np.outer(v, h.conj()) + np.outer(h, v.conj()))
    return np.array(out)


def top(hraw):
    ev, vec = np.linalg.eigh((hraw + hraw.conj().T)/2)
    sel = vec[:, ev == ev[-1]]
    proj = sel @ sel.conj().T
    for col in proj.T:
        if np.linalg.norm(col) > 0:
            h = normal(col)
            break
    j = int(np.argmax(abs(h)))
    return h * h[j].conjugate() / abs(h[j])


class RecordingRNG:
    def __init__(self, seed):
        self.rng = np.random.default_rng(seed)
        self.record = []

    def multinomial(self, n, p):
        counts = self.rng.multinomial(n, p)
        self.record.append((int(n), p.copy(), counts.copy()))
        return counts


def dense_ridge(records, D, ridge):
    B = basis(D)
    X, y = [], []
    for effects, counts in records:
        f = np.einsum('aij,kji->ak', effects, B).real
        # Expand every copy's full categorical residual, including unobserved labels.
        for label, count in enumerate(counts):
            for _ in range(int(count)):
                X.extend(f)
                y.extend(np.eye(len(effects))[label])
    X = np.r_[np.asarray(X), np.sqrt(ridge)*np.eye(D*D)]
    y = np.r_[np.asarray(y), np.zeros(D*D)]
    coeff = np.linalg.lstsq(X, y, rcond=None)[0]
    return np.einsum('k,kij->ij', coeff, B)


def dense_correction(h, records, ref, eta):
    T = tangent_frame(h)
    X, y = [], []
    floor = float(np.min(ref[:, 0, 0].real))/4
    for effects, counts in records:
        q = np.array([np.vdot(h, E @ h).real for E in effects])
        f = np.einsum('aij,kji->ak', effects, T).real
        inv_sqrt = 1/np.sqrt(np.maximum(q, floor))
        for label, count in enumerate(counts):
            for _ in range(int(count)):
                X.extend(f*inv_sqrt[:, None])
                y.extend((np.eye(len(effects))[label]-q)*inv_sqrt)
    X = np.r_[np.asarray(X), np.sqrt(eta)*np.eye(len(T))]
    y = np.r_[np.asarray(y), np.zeros(len(T))]
    step = np.linalg.lstsq(X, y, rcond=None)[0]
    delta = np.einsum('k,kij->ij', step, T)
    return normal(h + delta @ h), delta


def mixed_record_replay():
    theta = normal(np.array([1., 2., 3.]))*.9
    sizes = np.array([16, 17, 31, 64])
    horizons = np.cumsum(sizes)
    for rule in ['bures', 'frobenius']:
        rng = RecordingRNG(20261020)
        got, rows = mixed.trajectory(rule, theta, rng, horizons,
                                     ridge=.73, diagnostic=True, batch_sizes=sizes)
        X, y, c, n = [], [], np.zeros(3), 0
        for k, (size, supplied_p, counts) in enumerate(rng.record):
            if np.linalg.norm(c) == 0:
                axes = np.eye(3)[[2, 0, 1]]
            else:
                u = normal(c)
                v = u - np.array([0., 0., 1.])
                Q = np.eye(3) if np.linalg.norm(v) == 0 else np.eye(3)-2*P(v).real/np.dot(v, v)
                axes = np.array([u, Q[:, 0], Q[:, 1]])
            s = np.sqrt(1-c@c)
            pi = np.ones(3)/3 if rule == 'bures' else np.array([s, 1, 1])/(2+s)
            expected = np.array([pi[j]*(1+sign*axes[j]@theta)/2
                                 for j in range(3) for sign in [-1, 1]])
            near(supplied_p, expected)
            for index, count in enumerate(counts):
                j, b = divmod(index, 2)
                X.extend([axes[j]]*int(count))
                y.extend([2*b-1]*int(count))
            n += size
            raw = np.linalg.lstsq(np.r_[X, np.sqrt(.73)*np.eye(3)],
                                  np.r_[y, np.zeros(3)], rcond=None)[0]
            cap = 1 if rule == 'bures' else np.sqrt(1-(n+1)**(-.5))
            c = (raw if np.linalg.norm(raw) < cap else np.zeros(3)) if rule == 'bures' else (
                raw if np.linalg.norm(raw) <= cap else cap*normal(raw))
            near(raw, rows[k]['raw_estimate'])
            near(c, rows[k]['design_estimate'])
            pauli = np.array([[[0, 1], [1, 0]], [[0, -1j], [1j, 0]], [[1, 0], [0, -1]]])
            rho = (np.eye(2)+np.einsum('k,kij->ij', c, pauli))/2
            rho0 = (np.eye(2)+np.einsum('k,kij->ij', theta, pauli))/2
            near(got[k], n*np.array([np.linalg.norm(rho-rho0)**2, full_bures(rho, rho0)]))
    return {'rules': 2, 'batches_per_rule': 4, 'copies_per_rule': 128,
            'objective': 'individual binary records + augmented dense least squares',
            'loss_check': 'independent 2x2 density matrices and matrix-square-root Bures'}


def pure_record_replay():
    D = 4
    ref, _, _ = pure.reference_measurement(D)
    truth = normal(np.sqrt(np.arange(1, D+1))*np.exp(.37j*np.arange(D)))
    sizes = np.array([16, 16, 32, 64])
    horizons = np.cumsum(sizes)
    rng = RecordingRNG(20261021)
    got, _, _ = pure.trajectory(D, ref, truth, rng, horizons, ridge=.61,
                                correction_ridge=.47, batch_sizes=sizes)
    records, h = [], np.eye(D, dtype=complex)[:, 0]
    worst = 0.
    for k, (n, p, counts) in enumerate(rng.record):
        U = paper_frame(h)
        effects = U @ ref @ U.conj().T
        independent_p = np.array([np.vdot(truth, E @ truth).real for E in effects])
        near(p, independent_p)
        records.append((effects, counts))
        raw = dense_ridge(records, D, .61)
        h = top(raw)
        reported, _ = dense_correction(h, records, ref, .47)
        for method, v in enumerate([h, reported]):
            fidelity = abs(np.vdot(truth, v))**2
            expected = horizons[k]*np.array([2*(1-fidelity), 2*(1-np.sqrt(fidelity))])
            worst = max(worst, float(np.max(abs(got[k, method]-expected))))
            near(got[k, method], expected, atol=3e-9)
        batches = [estimators.OutcomeBatch(e, c) for e, c in records]
        production = estimators.weighted_tangent_update(h, batches, ref, .47)
        near(P(reported), production['state'])
    return {'dimension': D, 'batches': 4, 'copies': 128,
            'maximum_loss_difference': worst,
            'objective': 'expanded full categorical objective; independent Gram-Schmidt tangent basis; augmented least squares'}


def metamorphic_checks():
    rng = np.random.default_rng(20261022)
    ref, bases, labels = pure.reference_measurement(4)
    for D in [2, 3, 4, 7]:
        E, B, L = pure.reference_measurement(D)
        near(E.sum(0), np.eye(D))
        assert len(E) == 2*(D*D-D+1)*D
        near(E[:, 0, 0].real.min()/4, 1/(16*(D*D-D+1)*sum(j*j for j in range(1, D+1))))
        assert np.linalg.matrix_rank(np.einsum('aij,kji->ak', E, basis(D)).real) == D*D
        for h in [np.eye(D, dtype=complex)[0], np.eye(D, dtype=complex)[1],
                  -np.eye(D, dtype=complex)[0], normal(rng.normal(size=D)+1j*rng.normal(size=D))]:
            U = estimators.householder_frame(h)
            near(U.conj().T @ U, np.eye(D))
            near(U[:, 0], h)
    h = normal(rng.normal(size=4)+1j*rng.normal(size=4))
    A = paper_frame(h)
    E = A @ ref @ A.conj().T
    q = np.array([np.vdot(h, e@h).real for e in E])
    counts = rng.multinomial(71, q/q.sum())
    records = [estimators.OutcomeBatch(E, counts)]
    base = estimators.symmetric_gls_estimate(records, ref, .8, .4)
    repeated = [estimators.OutcomeBatch(E, counts*3)]
    scaled = estimators.symmetric_gls_estimate(repeated, ref, 2.4, 1.2)
    near(base['initial']['raw'], scaled['initial']['raw'])
    near(base['state'], scaled['state'])
    # A change of ambient coordinates must rotate each fitted physical state.
    V, _ = np.linalg.qr(rng.normal(size=(4, 4))+1j*rng.normal(size=(4, 4)))
    initial = estimators.least_squares_from_batches(records, 4, .8)
    rotated_records = [estimators.OutcomeBatch(V@E@V.conj().T, counts)]
    initial_rotated = estimators.least_squares_from_batches(rotated_records, 4, .8)
    near(initial_rotated['raw'], V@initial['raw']@V.conj().T)
    near(initial_rotated['state'], V@initial['state']@V.conj().T)
    # The clipping threshold belongs to the fixed reference, not to a renormalized q.
    h_bad = np.eye(4, dtype=complex)[1]
    fixed_counts = np.arange(len(ref), dtype=int) % 3
    bad_records = [estimators.OutcomeBatch(ref, fixed_counts)]
    clipped = estimators.weighted_tangent_update(h_bad, bad_records, ref, .4)
    assert clipped['clipped_batch_outcomes'] > 0
    independent, _ = dense_correction(h_bad, [(ref, fixed_counts)], ref, .4)
    near(clipped['state'], P(independent))
    # Check physical branch/basis/readout probabilities separately from joint effects.
    Vphase = np.diag([1j, 1, 1, 1])
    truth = normal(rng.normal(size=4)+1j*rng.normal(size=4))
    U = paper_frame(h)
    for idx, (b, ell, k) in enumerate(labels):
        v = U @ np.linalg.matrix_power(Vphase.conj().T, int(b)) @ bases[ell, :, k]
        physical = abs(np.vdot(v, truth))**2 / (2*len(bases))
        near(physical, np.vdot(truth, (U@ref[idx]@U.conj().T)@truth).real)
    # Largest algebraic, not largest absolute eigenvalue; ties remain deterministic.
    chosen = estimators.top_vector(np.diag([-100., 2., 2., -1.]))
    near(P(chosen), np.diag([0., 1., 0., 0.]))
    return {'reference_dimensions': [2, 3, 4, 7], 'householder_vectors': 16,
            'scaled_record_and_ridge_equivariance': True,
            'ambient_unitary_equivariance_of_preliminary_fit': True,
            'active_probability_clipping_dense_objective': True,
            'physical_branch_basis_Born_law_all_104_labels': True,
            'algebraic_eigenvalue_and_exact_tie_checks': True}


def truth_blindness():
    class RecordTape:
        def __init__(self): self.calls = 0
        def multinomial(self, n, p):
            counts = np.zeros(len(p), dtype=int)
            counts[(7*self.calls+3) % len(p)] = n
            self.calls += 1
            return counts
    sizes = np.array([16, 16, 32, 64])
    hs = np.cumsum(sizes)
    all_rows = []
    for rule in ['bures', 'frobenius']:
        pairs = []
        for truth in [np.array([.1, .2, .3]), np.array([-.2, .4, -.1])]:
            _, rows = mixed.trajectory(rule, truth, RecordTape(), hs, diagnostic=True, batch_sizes=sizes)
            pairs.append(rows)
        for a, b in zip(*pairs):
            for key in ['raw_estimate', 'design_estimate', 'next_axes', 'next_probabilities']:
                near(a[key], b[key])
        all_rows.append(True)
    ref, _, _ = pure.reference_measurement(4)
    outputs = []
    original = pure.correction
    def recorder(h, records, reference, ridge):
        result = original(h, records, reference, ridge)
        outputs.append((P(h), P(result)))
        return result
    for truth in [normal(np.ones(4, dtype=complex)), normal(np.array([1., 2j, 3., 4j]))]:
        with patch.object(pure, 'correction', recorder):
            pure.trajectory(4, ref, truth, RecordTape(), hs, batch_sizes=sizes)
    for a, b in zip(outputs[:4], outputs[4:]):
        near(a[0], b[0]); near(a[1], b[1])
    return {'mixed_both_rules_same_records_identical_designs': True,
            'pure_same_records_identical_preliminary_and_corrected_projectors': True,
            'truth_changed_only_sampling_diagnostic_and_loss_evaluation': True}


def fresh_runner_and_saved_data():
    config = json.loads((SIM/'configs/paper.json').read_text())
    config['replications'] = 4
    config['root_seed'] = 202610200713
    config['main_batch_schedule']['maximum'] = 256
    config['main_reporting_targets'] = [64, 128, 256]
    config['optional_covariance_dimensions'] = [2, 4]
    config['optional_reporting_powers'] = [6, 7, 8]
    config['optional_maximum_reporting_power'] = 8
    output = HERE / 'fresh_independent_samples'
    assert not output.exists(), 'Fresh evidence directory must not pre-exist.'
    log = io.StringIO()
    # Any attempt to load archived numerical arrays while generating data fails.
    with patch.object(np, 'load', side_effect=AssertionError('run must generate, not load arrays')):
        with contextlib.redirect_stdout(log):
            result = simulation.run(config, output)
    (HERE/'fresh_runner.log').write_text(log.getvalue())
    with np.load(output/'samples.npz', allow_pickle=False) as f:
        arrays = {k: f[k] for k in f.files}
    for study in ['mixed_bures', 'mixed_frobenius', 'pure_algorithm3']:
        values = arrays['pure_losses' if study == 'pure_algorithm3' else study+'_losses']
        for j, row in enumerate(result['studies'][study]['risks']):
            near(row['mean'], np.sum(values[:, j], axis=0)/4)
            mean = np.sum(values[:, j], axis=0)/4
            se = np.sqrt(np.sum((values[:, j]-mean)**2, axis=0)/(4*3))
            near(row['mc_se'], se)
    assert all(np.all(np.isfinite(a)) for a in arrays.values())
    assert arrays['mixed_bures_losses'].shape[0] == arrays['pure_losses'].shape[0] == 4
    with np.load(output/'pure_design_samples.npz', allow_pickle=False) as f:
        criteria = f['criteria']
    summary = json.loads((output/'pure_design_summary.json').read_text())
    for j, row in enumerate(summary['rows']):
        near(row['mean'], criteria[:, j].mean(0))
        near(row['mc_se'], criteria[:, j].std(0, ddof=1)/2)
    # Fresh independent regeneration of every role-1 stream is compared to stored arrays.
    hs = np.asarray(result['horizons'])
    sizes = np.asarray(result['main_batch_sizes'])
    theta = np.asarray(result['studies']['mixed_bures']['truth'])
    href = np.asarray(result['studies']['pure_algorithm3']['truth_real']) + 1j*np.asarray(result['studies']['pure_algorithm3']['truth_imag'])
    ref, _, _ = pure.reference_measurement(4)
    for rep in range(4):
        for experiment, rule in [(1, 'bures'), (2, 'frobenius')]:
            stream = np.random.default_rng(np.random.SeedSequence([config['root_seed'], experiment, 1, rep]))
            values, _ = mixed.trajectory(rule, theta, stream, hs, batch_sizes=sizes)
            near(values, arrays['mixed_'+rule+'_losses'][rep])
        stream = np.random.default_rng(np.random.SeedSequence([config['root_seed'], 3, 1, rep]))
        values, errors, _ = pure.trajectory(4, ref, href, stream, hs, diagnostic=True, batch_sizes=sizes)
        near(values, arrays['pure_losses'][rep])
        near(errors, arrays['pure_tangent_errors'][rep])
    from adaptive_tomography.plotting import render
    plot_log = io.StringIO()
    with contextlib.redirect_stdout(plot_log):
        render(output, HERE/'fresh_independent_figures')
    (HERE/'fresh_plot.log').write_text(plot_log.getvalue())
    return {'replications_per_study': 4, 'main_copies_per_replicate': 256,
            'studies': ['mixed_bures', 'mixed_frobenius', 'pure_algorithm3', 'optional_D2', 'optional_D4'],
            'array_loading_disabled_during_fresh_generation': True,
            'every_main_replicate_regenerated': True,
            'all_main_means_and_unbiased_MCSEs_recomputed': True,
            'all_pure_information_criteria_included_after_per_record_inversion': True,
            'three_figure_sets_rendered_from_fresh_samples': True,
            'root_seed': config['root_seed'], 'reduced_configuration': config}


def main():
    started = datetime.now(timezone.utc).isoformat()
    initial = sources()
    (HERE/'SOURCE_BASELINE.json').write_text(json.dumps(initial, indent=2)+'\n')
    checks = {}
    for name, function in [('mixed_dense_record_replay', mixed_record_replay),
                           ('pure_dense_record_replay', pure_record_replay),
                           ('metamorphic_and_adversarial', metamorphic_checks),
                           ('fixed_record_truth_blindness', truth_blindness),
                           ('fresh_generator_and_aggregation', fresh_runner_and_saved_data)]:
        checks[name] = function()
        print(name, 'PASS', flush=True)
    assert sources() == initial, 'Protected numerical/paper/Lean sources changed during audit.'
    receipt = {'status': 'PASS', 'review_date_America_Chicago': datetime.now(ZoneInfo('America/Chicago')).date().isoformat(),
               'started_utc': started, 'completed_utc': datetime.now(timezone.utc).isoformat(),
               'python': sys.version, 'numpy': np.__version__, 'checks': checks,
               'source_files_hash_checked': len(initial), 'protected_sources_unchanged': True,
               'independent_check_script_sha256': sha(SCRIPT),
               'limitations': ['Small finite tests do not prove asymptotic theorems.',
                               'This audit is not a formal verification of Python.',
                               'Archived arrays alone cannot authenticate their historical execution date.',
                               'This independent run does not replace the full 10000-replicate paper experiment.']}
    (HERE/'INDEPENDENT_CHECKS.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps({'status': 'PASS', 'checks': list(checks), 'source_files': len(initial)}))


if __name__ == '__main__':
    main()
